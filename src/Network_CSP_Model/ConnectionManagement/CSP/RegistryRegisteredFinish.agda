{-# OPTIONS --guardedness #-}

-- Conditional registered-event fixture, not an admission-derived producer trace.
-- InboundGovernor.hs MuxFinished branch at the established network source pin.
module ConnectionManagement.CSP.RegistryRegisteredFinish where

open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch)
open import ConnectionManagement.CSP.OriginRegistry using (Process; trace-intro)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryShutdown using (wrap)
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- The notification is already selected into the batch. Its producer and queue
-- selection are explicit fixture premises; mux status is varied independently.
runtime : M.Status → IG.Runtime
runtime status = IG.setMux G.mid (record G.armedMux { status = status })
  (Open.inboundGovernor G.registered)
snapshot : M.Status → IG.PC → IG.Published → State
snapshot status pc published = wrap (record G.registered
  { inboundGovernor = record (IG.setPC pc (runtime status)) { publishedState = published } })
input waiting decision removed : M.Status → State
input status = snapshot status (IG.readNext 10 (S.muxFinished key₀ ∷ [])) G.registeredState
waiting status = snapshot status (IG.waitStopped 10 [] key₀ G.mid G.registeredState) G.registeredState
decision status = snapshot status (IG.publishDecision 10 [] (IG.unregister key₀ G.registeredState)) G.registeredState
removed status = snapshot status (IG.readNext 10 []) (IG.unregister key₀ G.registeredState)

-- Reading captures the currently registered mux even when it is still ready.
read-path : ∀ status → Executes (input status) (dispatch (Open.igStep IG.readEvent) ∷ []) (waiting status)
read-path status = next refl done
schedule : List Action
schedule = map (λ a → dispatch (Open.igStep a))
  (IG.readEvent ∷ IG.pollStopped ∷ IG.commitDecision ∷ [])
stopped-path : Executes (input M.stopped) schedule (removed M.stopped)
stopped-path = next {s₁ = waiting M.stopped} refl (next {s₁ = decision M.stopped} refl (next refl done))
failed-path : ∀ err → Executes (input (M.failed err)) schedule (removed (M.failed err))
failed-path err = next {s₁ = waiting (M.failed err)} refl
  (next {s₁ = decision (M.failed err)} refl (next refl done))
stopped-trace : traces (Process (input M.stopped)) (map label schedule)
stopped-trace = trace-intro stopped-path
failed-trace : ∀ err → traces (Process (input (M.failed err))) (map label schedule)
failed-trace err = trace-intro (failed-path err)
