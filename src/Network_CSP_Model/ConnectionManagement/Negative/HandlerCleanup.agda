{-# OPTIONS --guardedness #-}

-- TIME_WAIT and failed-close control points cannot skip required finalization.
module ConnectionManagement.Negative.HandlerCleanup where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerLifecycle using (waiting)
open import ConnectionManagement.CSP.HandlerCleanup using (closeFailed; interrupted)
open import ConnectionManagement.Scenarios.Admission using (child₀)
import ConnectionManagement.Rules.Cleanup as C
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

wait-must-be-ready : advance (cleanupStep child₀ C.finishTimeWait) waiting ≡ nothing
wait-must-be-ready = refl
close-failure-cannot-publish : advance (cleanupStep child₀ C.publishCleanupMap) closeFailed ≡ nothing
close-failure-cannot-publish = refl
interruption-must-finalize : advance (cleanupStep child₀ C.readCleanupCounters) interrupted ≡ nothing
interruption-must-finalize = refl

no-premature-finalization : ¬ traces (Process waiting)
  (map label (cleanupStep child₀ C.finishTimeWait ∷ []))
no-premature-finalization = refused-extension {as = []} done wait-must-be-ready
no-failed-close-publication : ¬ traces (Process closeFailed)
  (map label (cleanupStep child₀ C.publishCleanupMap ∷ []))
no-failed-close-publication = refused-extension {as = []} done close-failure-cannot-publish
no-interrupted-finalizer-skip : ¬ traces (Process interrupted)
  (map label (cleanupStep child₀ C.readCleanupCounters ∷ []))
no-interrupted-finalizer-skip = refused-extension {as = []} done interruption-must-finalize
