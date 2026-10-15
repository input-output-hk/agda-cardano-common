{-# OPTIONS --guardedness #-}

-- The known good establishment path passes the executable success monitor.
module ConnectionManagement.CSP.OriginMonitorWitness where

open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (negotiated)
open import ConnectionManagement.Machine using (Action; handlerPublication; handlerStep; igStep; resultWritten)
open import ConnectionManagement.Rules.OriginMonitor
open import ConnectionManagement.Properties.OriginMonitor using (accepted-allocation; origin-retained)
open import ConnectionManagement.Properties.HandlerOrigin using (Origin)
open import ConnectionManagement.CSP.OriginMonitor
open import ConnectionManagement.CSP.Process using (Channel; label)
import ConnectionManagement.CSP.Process as OpenProcess
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.CSP.HandlerLifecycle using (cancelError)
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

selected : Target
selected = target child₀ (ident 0)
expected : Ticket
expected = ticket G.mid (G.proto ∷ []) duplex
initial installed completed : State
initial = start E.forked
installed = observed E.installed (awaitingPublication expected)
completed = observed E.completedState (published expected)
allocate : Action
allocate = igStep (IG.installHandle (ident 0) G.mid key₀ (G.proto ∷ []) duplex)
remaining : List Action
remaining = handlerPublication child₀ (negotiated (ident 0) duplex) resultWritten ∷
  handlerStep child₀ (L.attach cancelError) ∷ E.suffix
remaining-path : Executes selected installed remaining completed
remaining-path = next {s₁ = observed E.published (published expected)} refl
  (next {s₁ = observed E.attached (published expected)} refl
  (next {s₁ = observed E.mapPublished (published expected)} refl
  (next {s₁ = observed E.waiting (published expected)} refl
  (next {s₁ = observed E.readResult (published expected)} refl
  (next {s₁ = observed E.committed (published expected)} refl
  (next {s₁ = observed E.counted (published expected)} refl
  (next {s₁ = observed E.enqueued (published expected)} refl (next refl done))))))))
establish-path : Executes selected initial E.establish completed
establish-path = next {s₁ = installed} refl remaining-path
monitored-trace : traces (Process selected initial) (map label E.establish)
monitored-trace = trace-intro establish-path
projected-trace : traces (OpenProcess.Process E.forked) (map label E.establish)
projected-trace = trace-projects monitored-trace
installed-origin : Origin child₀ (ident 0) G.mid (G.proto ∷ []) duplex E.installed
installed-origin = accepted-allocation selected G.mid key₀ (G.proto ∷ []) duplex initial E.forked-resources refl
completed-origin : Origin child₀ (ident 0) G.mid (G.proto ∷ []) duplex E.completedState
completed-origin = origin-retained remaining-path installed-origin
