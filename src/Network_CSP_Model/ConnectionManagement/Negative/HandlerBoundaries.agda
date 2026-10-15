{-# OPTIONS --guardedness #-}

-- The raw process cannot realize overwriting a filled promise, repeating its
-- reported publication fault, or publishing after cleanup entry.
module ConnectionManagement.Negative.HandlerBoundaries where

open import Data.List using (map; []; _∷_)
open import Relation.Nullary using (¬_)
open import Process_Trees
open import ConnectionManagement.State using (query)
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerAttachment using (newlyAttached)
open import ConnectionManagement.CSP.HandlerOutcomes using (n₈)
open import ConnectionManagement.CSP.HandlerBoundaries using
  (duplicate; overwrite-refused; repeat-fault-refused; publication-after-exit-refused)
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

no-overwrite-trace : ¬ traces (Process newlyAttached)
  (map label (handlerPublication child₀ query resultWritten ∷ []))
no-overwrite-trace = refused-extension {as = []} done overwrite-refused

no-repeat-fault-trace : ¬ traces (Process duplicate)
  (map label (handlerPublication child₀ query duplicateWrite ∷ []))
no-repeat-fault-trace = refused-extension {as = []} done repeat-fault-refused

no-post-exit-publication-trace : ¬ traces (Process n₈)
  (map label (handlerPublication child₀ query duplicateWrite ∷ []))
no-post-exit-publication-trace = refused-extension {as = []} done publication-after-exit-refused
