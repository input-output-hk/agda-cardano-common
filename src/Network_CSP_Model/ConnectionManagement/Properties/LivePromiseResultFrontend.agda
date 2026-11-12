{-# OPTIONS --guardedness #-}

-- The exact content of an already published promise survives all frontend
-- events. This does not establish when a mux-frame phase first publishes it.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId; PromiseId)
import ConnectionManagement.State
module ConnectionManagement.Properties.LivePromiseResultFrontend
  (b io : ErrorId → Bool) (observedPromise : PromiseId)
  (observedResult : ConnectionManagement.State.HandshakeResult) where

open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Properties.CallerCancellation as Writer
import ConnectionManagement.Properties.SubsystemInvariant as Subsystem
import ConnectionManagement.Properties.ServerAdmissionInvariant as AdmissionLift
import ConnectionManagement.Properties.ServerAdmissionInvariants as AdmissionPaths
import ConnectionManagement.Properties.ServerIGExit as ExitLift
import ConnectionManagement.Properties.ServerPeersHandlerResources as FrontLift
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication

import ConnectionManagement.Properties.OutboundWorldInvariant as World
import ConnectionManagement.Properties.StateRetention as State
import ConnectionManagement.Properties.IGTableRetention as Tables
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Properties.OutboundAcquireEffects as AcquireEffects
import ConnectionManagement.Properties.SharedStateEffects as Effects
import ConnectionManagement.Rules.OutboundAcquire as AcquireRules

-- State retention preserves exactly this result, independently of allocation
-- counters, current entry constructors or present ownership.
Recorded : S.State → Set
Recorded s = lookup observedPromise (S.handshakeResults s) ≡ just observedResult
Predicate : S.State → IG.Runtime → Set
Predicate s ig = Recorded s
stable : ∀ {s s′ ig ig′} → State.Retains s s′ → Tables.Retains ig ig′ → Predicate s ig → Predicate s′ ig′
stable state tables = State.resultsRetained state observedPromise observedResult
module Outbound where
 open World.Lift Predicate stable public
 RuntimeValid : AcquireRules.Runtime → S.State → Set
 RuntimeValid acquiring s = Recorded s
module Acquire where
 step-preserves : ∀ w mode action f s {f′ s′} → Recorded s →
   AcquireRules.step w mode action f s ≡ just (f′ , s′) → Recorded s′
 step-preserves w mode action f s {s′ = s′} recorded actual = State.resultsRetained {s = s} {s′ = s′}
   (Effects.to-retains {s = s} {s′ = s′} (AcquireEffects.step-effects w mode action f s actual)) observedPromise observedResult recorded

private
 module N = Publication b
 module E = Exit b
 module A = AdmissionLift b

-- Physical actions project to finite source executions, including coupled
-- acknowledgement and startup-fault routes.
lower-preserves : ∀ a n {n′} → N.step a n ≡ just n′ →
  Outbound.Valid (N.source n) → Outbound.Valid (N.source n′)
lower-preserves a n actual valid = Outbound.exec-preserves valid
  (proj₂ (AdmissionPaths.lower-path b a n actual))
-- Server handoff changes admissions and sockets only.
admit-preserves : ∀ w req c → Outbound.Valid c → Outbound.Valid (A.admitSource w req c)
admit-preserves w req c valid = valid
-- Closing a socket retains every published result.
socket-preserves : ∀ sock owner c → Outbound.Valid c → Outbound.Valid (A.socketSource sock owner c)
socket-preserves sock owner c valid = valid
open A.Lift Outbound.Valid lower-preserves admit-preserves socket-preserves
  using () renaming (step-preserves to server-preserves)
-- IG exit clears pending continuations without rewriting results.
clear-preserves : ∀ c → Outbound.Valid c → Outbound.Valid (E.clearPending c)
clear-preserves c valid = valid
open ExitLift.Lift b Outbound.Valid server-preserves clear-preserves
  using () renaming (step-preserves to ig-exit-preserves)
open Subsystem.Lift Outbound.RuntimeValid Outbound.advance-preserves
  using () renaming (advance-preserves to subsystem-preserves)

-- Detached cleanup executes an acquisition action against the shared world.
cleanup-preserves : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) →
  Outbound.Valid c → Outbound.Valid c′
cleanup-preserves action f c actual valid with Writer.step-writer action f c actual
... | Writer.writer active active′ shared′ before source frameEq machineEq = subst
  (λ out → Outbound.Valid out) (sym machineEq)
  (Acquire.step-preserves (Cancel.caller f) (M.responder (O.core c))
    (Cancel.acquireAction action) active (M.world (O.core c)) valid source)
-- Caller detachment retains the complete shared core.
start-preserves : ∀ w err context c {f c′} → Cancel.start w err context c ≡ just (f , c′) →
  Outbound.Valid c → Outbound.Valid c′
start-preserves w err context c actual valid = subst (λ core → Recorded (M.world core))
  (sym (Writer.start-core w err context c actual)) valid

open FrontLift.Observer b io Outbound.RuntimeValid subsystem-preserves
  cleanup-preserves start-preserves ig-exit-preserves public using (module Frontend)
