{-# OPTIONS --guardedness #-}

-- IG unregistration, pool closure and socket closure are distinct boundaries.
module ConnectionManagement.Negative.RegistryReturn where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.CSP.OriginRegistry using (Process; refused-extension)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryReturn
open import ConnectionManagement.CSP.RegistryShutdown using (wrap; append-path)
open import ConnectionManagement.Negative.RegistryShutdown using (delivered-prefix; delivered-path)
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.Fixtures as F
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- The refusal is after an admission-derived CSP prefix, not an arbitrary state.
returned-prefix : List Action
returned-prefix = delivered-prefix ++ caller
returned-path : Executes (start F.start) returned-prefix (wrap Life.callerPublished)
returned-path = append-path delivered-path caller-path
exit-refused : step (dispatch (Open.handlerExit child₀)) (wrap Life.callerPublished) ≡ nothing
exit-refused = refl
no-premature-exit : ¬ traces (Process (start F.start))
  (map label (returned-prefix ++ (dispatch (Open.handlerExit child₀) ∷ [])))
no-premature-exit = refused-extension returned-path exit-refused

-- Return hands a decision to IG; only commitDecision removes registration.
return-retains-registration : IG.publishedState (Open.inboundGovernor Life.callerReturned) ≡ G.registeredState
return-retains-registration = refl
unregistered : IG.connections (IG.publishedState (Open.inboundGovernor Life.callerPublished)) ≡ []
unregistered = refl
pool-not-closed : Life.handlerPhase Life.callerPublished ≡ just L.poolClosing
pool-not-closed = refl
socket-still-owned : lookup (ident 0) (S.sockets (Open.world Life.callerPublished)) ≡ just (S.handling child₀)
socket-still-owned = refl
cleanup-not-entered : S.cleanups (Open.world Life.callerPublished) ≡ []
cleanup-not-entered = refl

-- The final mux callback can enqueue its dead event without an IG descriptor.
tracer-after-unregistration : S.inboundInfo (Open.world (returnedState Life.traced)) ≡ S.muxFinished key₀ ∷ []
tracer-after-unregistration = refl
final-unregistered : IG.connections (IG.publishedState (Open.inboundGovernor (returnedState Life.doneCleanup))) ≡ []
final-unregistered = refl
final-socket : lookup (ident 0) (S.sockets (Open.world (returnedState Life.doneCleanup))) ≡ just S.closed
final-socket = refl
final-map : S.mapCell (S.cm (Open.world (returnedState Life.doneCleanup))) ≡ S.full []
final-map = refl
final-cleanup : lookup child₀ (S.cleanups (Open.world (returnedState Life.doneCleanup))) ≡ just (S.cleanupDone S.cleanupNormal)
final-cleanup = refl
