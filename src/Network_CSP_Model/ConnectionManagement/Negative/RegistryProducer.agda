{-# OPTIONS --guardedness #-}

-- Reachable producer/consumer boundaries, without injected notifications.
module ConnectionManagement.Negative.RegistryProducer where

open import Data.List using ([]; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (dispatch)
open import ConnectionManagement.CSP.OriginRegistry using (Process; refused-extension)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryProducer
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.CSP.HandlerOutcomes as Out
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.Fixtures as F
open import ConnectionManagement.Scenarios.Admission using (key₀; child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

producer-order : notifications ≡
  S.miniProtocolTerminated (S.terminatedProtocol key₀ G.mid G.proto duplex (S.errored Out.err)) ∷
  S.muxFinished key₀ ∷ []
producer-order = refl
registration-before-poll : IG.publishedState (Open.inboundGovernor (machine muxRead)) ≡
  IG.publishedState (Open.inboundGovernor failureState)
registration-before-poll = refl
captured-current-mux : IG.continuation (Open.inboundGovernor (machine muxRead)) ≡
  IG.waitStopped 12 [] key₀ G.mid (IG.publishedState armed)
captured-current-mux = refl
final-unregistered : IG.connections (IG.publishedState (Open.inboundGovernor (machine ready))) ≡ []
final-unregistered = refl
handler-not-unwound : Life.handlerPhase (machine ready) ≡ just L.monitoring
handler-not-unwound = refl
exit-refused : step (dispatch (Open.handlerExit child₀)) ready ≡ nothing
exit-refused = refl
no-premature-exit : ¬ traces (Process (start F.start))
  (map label (schedule ++ (dispatch (Open.handlerExit child₀) ∷ [])))
no-premature-exit = refused-extension path exit-refused
