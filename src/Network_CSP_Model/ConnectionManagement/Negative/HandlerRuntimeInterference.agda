{-# OPTIONS --guardedness #-}

-- Reference evidence can survive cleanup and stopping while readiness is lost.
module ConnectionManagement.Negative.HandlerRuntimeInterference where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerRuntimeInterference
open import ConnectionManagement.CSP.HandlerLifecycle using (cancelError)
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import ConnectionManagement.Scenarios.Handshake using (success)
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- cleaned-prepared certifies retained references, not a live publication body.
publication-refused : advance (handlerPublication child₀ success resultWritten) cleaned ≡ nothing
publication-refused = refl
no-publication : ¬ traces (Process cleaned) (map label (handlerPublication child₀ success resultWritten ∷ []))
no-publication = refused-extension {as = []} done publication-refused
no-implicit-tracking : ¬ TrackedChain child₀ cleaned
no-implicit-tracking (f , () , ch)

-- stopped-prepared still exists, but attachment requires a ready mux and a
-- returned callback. Do not turn the preservation theorem into an enabledness claim.
stopped-attach-refused : advance (handlerStep child₀ (L.attach cancelError)) stoppedState ≡ nothing
stopped-attach-refused = refl
no-stopped-attachment : ¬ traces (Process stoppedState)
  (map label (handlerStep child₀ (L.attach cancelError) ∷ []))
no-stopped-attachment = refused-extension {as = []} done stopped-attach-refused
