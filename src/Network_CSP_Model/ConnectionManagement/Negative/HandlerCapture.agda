{-# OPTIONS --guardedness #-}

-- Countermodels to dropping/retargeting the stored capture, not source bugs.
module ConnectionManagement.Negative.HandlerCapture where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Maybe.Properties using (just-injective)
open import ConnectionManagement.Domain
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Fixtures using (start)
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import ConnectionManagement.Properties.HandlerCapture using (Retains)
open import ConnectionManagement.Properties.HandlerCaptureInvariant using (exec-retains)
import ConnectionManagement.Rules.HandlerLifecycle as L

-- Minimal snapshots isolate the capture theorem from full runtime validity.
originalFrame changedFrame : L.Frame
originalFrame = L.frame (ident 0) (errorId 7) L.monitoring
changedFrame = L.frame (ident 1) (errorId 7) L.monitoring
original retargeted forgotten : Configuration
original = record start { handlerLifecycles = (child₀ , originalFrame) ∷ [] }
retargeted = record start { handlerLifecycles = (child₀ , changedFrame) ∷ [] }
forgotten = record start { handlerLifecycles = [] }
retargeting-violates-retention : ¬ Retains (handlerLifecycles original) (handlerLifecycles retargeted)
retargeting-violates-retention retains with retains child₀ originalFrame refl
... | g , found , same with just-injective found
...   | refl with same
...     | ()
forgetting-violates-retention : ¬ Retains (handlerLifecycles original) (handlerLifecycles forgotten)
forgetting-violates-retention retains with retains child₀ originalFrame refl
... | g , () , same

-- Quantify over ALL finite action sequences, not merely a supplied replay.
no-retargeting-execution : ∀ {as} → ¬ Executes original as retargeted
no-retargeting-execution path = retargeting-violates-retention (exec-retains path)
no-forgetting-execution : ∀ {as} → ¬ Executes original as forgotten
no-forgetting-execution path = forgetting-violates-retention (exec-retains path)
