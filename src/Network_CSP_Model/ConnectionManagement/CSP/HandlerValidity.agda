{-# OPTIONS --guardedness #-}

-- Every state of selected finite executions passes the diagnostic predicate.
-- This does not assert preservation for every Machine action/interleaving.
module ConnectionManagement.CSP.HandlerValidity where

open import Relation.Binary.PropositionalEquality using (refl)
open import ConnectionManagement.CSP.CheckedExecution
import ConnectionManagement.Properties.HandlerValidity as V
import ConnectionManagement.CSP.HandlerLifecycle as A
import ConnectionManagement.CSP.HandlerOutcomes as S

async-valid : Along V.valid A.unwind-path
async-valid = checked V.valid A.unwind-path refl
async-tracked : Along V.fullyTracked (tailRun A.unwind-path)
async-tracked = checked V.fullyTracked (tailRun A.unwind-path) refl
async-cleanup-tracked : Along V.fullyTracked A.cleanup-path
async-cleanup-tracked = checked V.fullyTracked A.cleanup-path refl
pruning-tracked : Along V.fullyTracked (tailRun A.pruned-unwind-path)
pruning-tracked = checked V.fullyTracked (tailRun A.pruned-unwind-path) refl
pruning-cleanup-tracked : Along V.fullyTracked A.pruned-cleanup-path
pruning-cleanup-tracked = checked V.fullyTracked A.pruned-cleanup-path refl
normal-valid : Along V.valid S.normal-path
normal-valid = checked V.valid S.normal-path refl
normal-tracked : Along V.fullyTracked (tailRun S.normal-path)
normal-tracked = checked V.fullyTracked (tailRun S.normal-path) refl
sync-valid : Along V.valid S.sync-path
sync-valid = checked V.valid S.sync-path refl
sync-tracked : Along V.fullyTracked (tailRun S.sync-path)
sync-tracked = checked V.fullyTracked (tailRun S.sync-path) refl
peer-tracked : Along V.fullyTracked S.peer-path
peer-tracked = checked V.fullyTracked S.peer-path refl
node-tracked : Along V.fullyTracked S.node-path
node-tracked = checked V.fullyTracked S.node-path refl
tracer-tracked : Along V.fullyTracked S.tracer-failure-path
tracer-tracked = checked V.fullyTracked S.tracer-failure-path refl

-- Attach before the first monitor action, so startup is covered too. Admission
-- and IG registration remain the existing source-composed prefix.
open import Data.List using (List; []; _∷_; _++_; map; drop)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence
open import ConnectionManagement.CSP.Fixtures using (start)
open import ConnectionManagement.Scenarios.Admission using (child₀)
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.IGRuntime as R
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

trackedStartActions : List Action
trackedStartActions = handlerStep child₀ (L.attach A.cancelError) ∷ R.startActions
tracked-start : Executes G.registered trackedStartActions S.s₀
tracked-start = next {c₁ = A.tracked L.monitoring G.registered} refl
  (next {c₁ = A.tracked L.monitoring R.commandRead} refl
  (next {c₁ = A.tracked L.monitoring R.callbackEntered} refl
  (next {c₁ = A.tracked L.monitoring R.activeSampled} refl
  (next {c₁ = A.tracked L.monitoring R.traceCommitted} refl
  (next {c₁ = A.tracked L.monitoring R.statusRunning} refl (next refl done))))))
startup-tracked : Along V.fullyTracked (tailRun tracked-start)
startup-tracked = checked V.fullyTracked (tailRun tracked-start) refl

-- Continuous post-attachment coverage through startup, error and node policy.
tracked-node-run : Executes (A.tracked L.monitoring G.registered)
  (R.startActions ++ (drop 1 S.syncActions ++ S.nodeActions)) S.nodeCleanup
tracked-node-run = exec-append (tailRun tracked-start)
  (exec-append (tailRun S.sync-path) S.node-path)
tracked-node-valid : Along V.fullyTracked tracked-node-run
tracked-node-valid = checked V.fullyTracked tracked-node-run refl
tracked-node-source-prefix : traces (Process start)
  (map label (G.lifecycle ++ (handlerStep child₀ (L.attach A.cancelError) ∷
     (R.startActions ++ (drop 1 S.syncActions ++ S.nodeActions)))))
tracked-node-source-prefix = trace-intro
  (exec-append G.lifecycle-path (next refl tracked-node-run))
