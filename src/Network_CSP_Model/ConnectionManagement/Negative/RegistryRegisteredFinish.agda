{-# OPTIONS --guardedness #-}

-- A notification is not itself proof that its captured mux has stopped.
module ConnectionManagement.Negative.RegistryRegisteredFinish where

open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (dispatch)
open import ConnectionManagement.CSP.OriginRegistry using (Process; refused-extension)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryRegisteredFinish
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.CSP.HandlerLifecycle using (cancelError)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Domain
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

ready-refused : step (dispatch (Open.igStep IG.pollStopped)) (waiting M.ready) ≡ nothing
ready-refused = refl
stopping-refused : step (dispatch (Open.igStep IG.pollStopped)) (waiting M.stopping) ≡ nothing
stopping-refused = refl
no-ready-poll : ¬ traces (Process (input M.ready))
  (map label (dispatch (Open.igStep IG.readEvent) ∷ dispatch (Open.igStep IG.pollStopped) ∷ []))
no-ready-poll = refused-extension (read-path M.ready) ready-refused
no-stopping-poll : ¬ traces (Process (input M.stopping))
  (map label (dispatch (Open.igStep IG.readEvent) ∷ dispatch (Open.igStep IG.pollStopped) ∷ []))
no-stopping-poll = refused-extension (read-path M.stopping) stopping-refused

-- Even a failed mux must pass through polling before decision publication.
commit-refused : step (dispatch (Open.igStep IG.commitDecision)) (waiting (M.failed cancelError)) ≡ nothing
commit-refused = refl
no-premature-commit : ¬ traces (Process (input (M.failed cancelError)))
  (map label (dispatch (Open.igStep IG.readEvent) ∷ dispatch (Open.igStep IG.commitDecision) ∷ []))
no-premature-commit = refused-extension (read-path (M.failed cancelError)) commit-refused
poll-retains-registration : ∀ status → IG.publishedState (Open.inboundGovernor (machine (decision status))) ≡ G.registeredState
poll-retains-registration status = refl
commit-removes-registration : ∀ status → IG.connections (IG.publishedState (Open.inboundGovernor (machine (removed status)))) ≡ []
commit-removes-registration status = refl
socket-still-owned : ∀ status → lookup (ident 0) (S.sockets (Open.world (machine (removed status)))) ≡ just (S.handling child₀)
socket-still-owned status = refl
no-release-frame : ∀ status → Open.inboundRelease (machine (removed status)) ≡ nothing
no-release-frame status = refl
