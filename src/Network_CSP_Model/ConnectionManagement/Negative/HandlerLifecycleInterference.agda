{-# OPTIONS --guardedness #-}

-- Preparation remains available while lifecycle guards refuse unsafe ordering.
module ConnectionManagement.Negative.HandlerLifecycleInterference where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerLifecycleInterference
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.Rules.HandlerLifecycle as L
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- received-prepared does not enable failure publication before joining jobs.
no-failure-before-join : ¬ traces (Process Life.received)
  (map label (handlerStep child₀ L.publishAsyncFailure ∷ []))
no-failure-before-join = refused-extension {as = []} done Life.no-failure-before-join
no-cleanup-before-unwind : ¬ traces (Process Life.received)
  (map label (handlerExit child₀ ∷ []))
no-cleanup-before-unwind = refused-extension {as = []} done Life.no-cleanup-before-unwind
-- finalized-prepared does not imply a second lifecycle attachment can succeed.
reattach-refused : advance (handlerStep child₀ (L.attach Life.cancelError)) Life.doneCleanup ≡ nothing
reattach-refused = refl
no-reattachment : ¬ traces (Process Life.doneCleanup)
  (map label (handlerStep child₀ (L.attach Life.cancelError) ∷ []))
no-reattachment = refused-extension {as = []} done reattach-refused
