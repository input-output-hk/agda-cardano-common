{-# OPTIONS --guardedness #-}

-- Attribution rejects traces whose erased allocation is otherwise accepted.
module ConnectionManagement.Negative.AttributedOrigin where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (negotiated)
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Rules.OriginMonitor using (observed; published; State)
import ConnectionManagement.Rules.OriginMonitor as Single
open import ConnectionManagement.Rules.AttributedOrigin
open import ConnectionManagement.Properties.AttributedOrigin using (reachable)
open import ConnectionManagement.Properties.OriginMonitorInvariant using (Invariant)
open import ConnectionManagement.CSP.AttributedOrigin
open import ConnectionManagement.CSP.OriginMonitorWitness using (selected; expected; initial; installed; completed)
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.CSP.HandlerLifecycle using (cancelError)
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)
import ConnectionManagement.Negative.OriginMonitorInvariant

allocation : Action
allocation = allocate child₀ (ident 0) G.mid key₀ (G.proto ∷ []) duplex
remaining : List Action
remaining = dispatch (Open.handlerPublication child₀ (negotiated (ident 0) duplex) Open.resultWritten) ∷
  dispatch (Open.handlerStep child₀ (L.attach cancelError)) ∷ map dispatch E.suffix
remaining-path : Executes selected installed remaining completed
remaining-path = next {s₁ = observed E.published (published expected)} refl
  (next {s₁ = observed E.attached (published expected)} refl
  (next {s₁ = observed E.mapPublished (published expected)} refl
  (next {s₁ = observed E.waiting (published expected)} refl
  (next {s₁ = observed E.readResult (published expected)} refl
  (next {s₁ = observed E.committed (published expected)} refl
  (next {s₁ = observed E.counted (published expected)} refl
  (next {s₁ = observed E.enqueued (published expected)} refl (next refl done))))))))
path : Executes selected initial (allocation ∷ remaining) completed
path = next {s₁ = installed} refl remaining-path
accepted-trace : traces (Process selected initial) (map label (allocation ∷ remaining))
accepted-trace = trace-intro path
completed-invariant : Invariant selected completed
completed-invariant = reachable path E.forked-resources

-- Erasure accepts this allocation; the new visible worker claim is inconsistent.
wrong-owner : Action
wrong-owner = allocate (ident 1) (ident 0) G.mid key₀ (G.proto ∷ []) duplex
erased-accepted : Single.step selected (erase wrong-owner) initial ≡ just installed
erased-accepted = refl
wrong-owner-refused : step selected wrong-owner initial ≡ nothing
wrong-owner-refused = refl
no-wrong-owner : ¬ traces (Process selected initial) (map label (wrong-owner ∷ []))
no-wrong-owner = refused-extension {as = []} done wrong-owner-refused

raw-bypass : Action
raw-bypass = dispatch (erase allocation)
raw-bypass-refused : step selected raw-bypass initial ≡ nothing
raw-bypass-refused = refl
no-raw-bypass : ¬ traces (Process selected initial) (map label (raw-bypass ∷ []))
no-raw-bypass = refused-extension {as = []} done raw-bypass-refused

wrong-handle : Action
wrong-handle = allocate child₀ (ident 1) (ident 1) key₀ (G.proto ∷ []) duplex
wrong-handle-refused : step selected wrong-handle initial ≡ nothing
wrong-handle-refused = refl
no-wrong-handle : ¬ traces (Process selected initial) (map label (wrong-handle ∷ []))
no-wrong-handle = refused-extension {as = []} done wrong-handle-refused
