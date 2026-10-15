{-# OPTIONS --guardedness #-}

-- Malformed fixtures expose attachment's creation premises; they do not
-- constitute executions from the initial configuration or Haskell defects.
module ConnectionManagement.Negative.HandlerReferences where

open import Data.Bool using (false)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.IGRegistration using (registered; armedMux; mid)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; cancelError)
open import ConnectionManagement.Scenarios.Admission using (child₀; key₁)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Properties.HandlerValidity as V

wrongKey missingEntry missingSocket : Configuration
wrongKey = record registered { inboundGovernor = IG.setMux mid
  (record armedMux { key = key₁ }) (inboundGovernor registered) }
missingEntry = record registered { world = record (world registered)
  { cm = record (cm (world registered)) { entries = [] } } }
missingSocket = record registered { world = record (world registered) { sockets = [] } }

wrong-key-attaches : advance (handlerStep child₀ (L.attach cancelError)) wrongKey ≡
  just (tracked L.monitoring wrongKey)
wrong-key-attaches = refl
missing-entry-attaches : advance (handlerStep child₀ (L.attach cancelError)) missingEntry ≡
  just (tracked L.monitoring missingEntry)
missing-entry-attaches = refl
missing-socket-attaches : advance (handlerStep child₀ (L.attach cancelError)) missingSocket ≡
  just (tracked L.monitoring missingSocket)
missing-socket-attaches = refl

wrong-key-invalid : V.valid (tracked L.monitoring wrongKey) ≡ false
wrong-key-invalid = refl
missing-entry-invalid : V.valid (tracked L.monitoring missingEntry) ≡ false
missing-entry-invalid = refl
missing-socket-invalid : V.valid (tracked L.monitoring missingSocket) ≡ false
missing-socket-invalid = refl
