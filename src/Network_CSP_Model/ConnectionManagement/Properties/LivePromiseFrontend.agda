{-# OPTIONS --guardedness #-}

-- Carry allocated-promise membership through the actual frontend. Component
-- source executions cover the physical layers; generic observer lifts cover
-- Server writes, caller cancellation and peer/frontend bookkeeping.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId; PromiseId)
module ConnectionManagement.Properties.LivePromiseFrontend
  (b io : ErrorId → Bool) (observedPromise : PromiseId) where

open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import ConnectionManagement.Properties.LivePromiseCore observedPromise using
  (Allocated; module Outbound; module Acquire)
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
-- Server handoff writes admissions and sockets, retaining the promise list.
admit-preserves : ∀ w req c → Outbound.Valid c → Outbound.Valid (A.admitSource w req c)
admit-preserves w req c valid = valid
-- Closing a socket retains every allocated promise.
socket-preserves : ∀ sock owner c → Outbound.Valid c → Outbound.Valid (A.socketSource sock owner c)
socket-preserves sock owner c valid = valid
open A.Lift Outbound.Valid lower-preserves admit-preserves socket-preserves
  using () renaming (step-preserves to server-preserves)
-- IG exit clears pending continuations without removing promise cells.
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
start-preserves w err context c actual valid = subst (λ core → Allocated (M.world core))
  (sym (Writer.start-core w err context c actual)) valid

open FrontLift.Observer b io Outbound.RuntimeValid subsystem-preserves
  cleanup-preserves start-preserves ig-exit-preserves public using (module Frontend)
