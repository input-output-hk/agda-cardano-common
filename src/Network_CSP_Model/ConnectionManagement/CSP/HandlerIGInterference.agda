{-# OPTIONS --guardedness #-}

-- Unattached preparation survives the IG loop and partial startup failure.
-- Finite traces establish reference safety, not eventual attachment.
module ConnectionManagement.CSP.HandlerIGInterference where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerEstablishment using (Prepared)
open import ConnectionManagement.Properties.HandlerRuntimeInterference
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro)
import ConnectionManagement.Properties.LoopRetention as Loop
import ConnectionManagement.Properties.StartupRetention as Startup
import ConnectionManagement.CSP.HandlerRuntimeInterference as RuntimeProof
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.IGRuntime as Runtime
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- This existing installation fixture is reachable within the model via
-- G.lifecycle-path. Its local certificate assumes no attached lifecycle frame.
installed-prepared : Prepared child₀ (ident 0) G.mid (world G.installed) (inboundGovernor G.installed)
installed-prepared = record
  { resources = record { original = _; found = refl; entryExists = _ , refl; socketExists = _ , refl }
  ; hd = _; mx = _; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl }
registrationActions : List Action
registrationActions = igStep (IG.captureTime 10) ∷ igStep IG.registerInactivity ∷
  igStep IG.selectBatch ∷ igStep IG.readEvent ∷ igStep IG.registerIdleTimer ∷ igStep IG.runResponders ∷ []
registration-covered : Interference registrationActions
registration-covered = more (loop Loop.capture) (more (loop Loop.inactivity)
  (more (loop Loop.select) (more (loop Loop.read) (more (loop Loop.idleTimer)
  (more (startup Startup.start) empty)))))
registration-path : Executes G.installed registrationActions G.registered
registration-path = next {c₁ = G.timeRead} refl (next {c₁ = G.timerArmed} refl
  (next {c₁ = G.drained} refl (next {c₁ = G.eventRead} refl
  (next {c₁ = G.prepared} refl (next refl done)))))
registered-prepared : Prepared child₀ (ident 0) G.mid (world G.registered) (inboundGovernor G.registered)
registered-prepared = prepared-exec registration-covered registration-path installed-prepared
running-prepared : Prepared child₀ (ident 0) G.mid (world Runtime.jobRunning) (inboundGovernor Runtime.jobRunning)
running-prepared = prepared-exec RuntimeProof.start-covered Runtime.start-path registered-prepared
registration-start-csp : Process G.installed ⟹⟨ map label (registrationActions ++ Runtime.startActions) ⟩ Process Runtime.jobRunning
registration-start-csp = exec-intro (exec-append registration-path Runtime.start-path)
running-unattached : handlerLifecycles Runtime.jobRunning ≡ []
running-unattached = refl

-- A local two-protocol fixture: the first starts, the second is already busy.
-- No claim is made that this input is reached by the whole admission trace.
failure-prepared : Prepared child₀ (ident 0) G.mid (world Runtime.failureInput) (inboundGovernor Runtime.failureInput)
failure-prepared = record
  { resources = record { original = _; found = refl; entryExists = _ , refl; socketExists = _ , refl }
  ; hd = _; mx = _; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl }
failureActions : List Action
failureActions = igStep IG.runResponders ∷ igStep IG.requestFailedStop ∷ []
failure-covered : Interference failureActions
failure-covered = more (startup Startup.start) (more (startup Startup.failedStop) empty)
failed-prepared : Prepared child₀ (ident 0) G.mid (world Runtime.stopRequested) (inboundGovernor Runtime.stopRequested)
failed-prepared = prepared-exec failure-covered Runtime.failed-start-path failure-prepared
failure-csp : Process Runtime.failureInput ⟹⟨ map label failureActions ⟩ Process Runtime.stopRequested
failure-csp = exec-intro Runtime.failed-start-path
failed-unattached : handlerLifecycles Runtime.stopRequested ≡ []
failed-unattached = refl
