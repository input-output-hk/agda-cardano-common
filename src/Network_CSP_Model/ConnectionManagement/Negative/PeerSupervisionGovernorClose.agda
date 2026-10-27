{-# OPTIONS --guardedness #-}

-- Nonempty physical-registry closure, layered over checked scenario controls.
module ConnectionManagement.Negative.PeerSupervisionGovernorClose where
open import ConnectionManagement.Negative.PeerSupervisionScenarios public
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.State as S
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.CSP.OutboundAdmission as O
import ConnectionManagement.Negative.GovernorPool as Prior
import ConnectionManagement.Properties.AsyncScope as ScopeFacts
-- Nonempty initialized supervision close. The governor's returned body finishes
-- its masked publication/deregistration while cancellation is pending. Only
-- after its captured Async is joined do provider and physical monitor scopes
-- close. Both final pool snapshots contain a real initialized child.
closing1 : PS.State
closing1 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing GP.Pool.openPool [] [] [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads0 (Scope.closing Scope.churn) false)
closing-step1 : PS.step (PS.scope Scope.beginUnwind) m4 ≡ just closing1
closing-step1 = refl
closing2 : PS.State
closing2 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing GP.Pool.openPool [] [] [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads1 (Scope.closing Scope.churn) true)
closing-step2 : PS.step (PS.scope Scope.requestCancel) closing1 ≡ just closing2
closing-step2 = refl
closing3 : PS.State
closing3 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing GP.Pool.openPool [] [] [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads2 (Scope.closing Scope.churn) true)
closing-step3 : PS.step (PS.scope Scope.deliverCancel) closing2 ≡ just closing3
closing-step3 = refl
closing4 : PS.State
closing4 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing GP.Pool.openPool [] [] [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads3 (Scope.closing Scope.churn) true)
closing-step4 : PS.step (PS.scope (Scope.bodyExit Scope.churn)) closing3 ≡ just closing4
closing-step4 = refl
closing5 : PS.State
closing5 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing GP.Pool.openPool [] [] [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads4 (Scope.closing Scope.churn) true)
closing-step5 : PS.step (PS.scope (Scope.publishResult Scope.churn)) closing4 ≡ just closing5
closing-step5 = refl
closing6 : PS.State
closing6 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing GP.Pool.openPool [] [] [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads5 (Scope.closing Scope.governor) false)
closing-step6 : PS.step (PS.scope Scope.join) closing5 ≡ just closing6
closing-step6 = refl
closing7 : PS.State
closing7 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing GP.Pool.openPool [] [] [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads6 (Scope.closing Scope.governor) true)
closing-step7 : PS.step (PS.scope Scope.requestCancel) closing6 ≡ just closing7
closing-step7 = refl
closing8 : PS.State
closing8 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing GP.Pool.openPool [] [] [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
closing-step8 : PS.step (PS.scope Scope.deliverCancel) closing7 ≡ just closing8
closing-step8 = refl
closing9 : PS.State
closing9 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing GP.Pool.closing (j₀ ∷ []) (j₀ ∷ []) [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
closing-step9 : PS.step (PS.run (GP.beginClose (j₀ ∷ []))) closing8 ≡ just closing9
closing-step9 = refl
closing10 : PS.State
closing10 = PS.supervising
  (GP.supervised (GP.Production.initial L.c40)
    (GP.Pool.poolState ((j₀ , (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))) ∷ []) (j₀ ∷ []) nothing (GP.Pool.cancelPending j₀) (j₀ ∷ []) (j₀ ∷ []) [] [])
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
closing-step10 : PS.step (PS.run GP.requestCancel) closing9 ≡ just closing10
closing-step10 = refl
closing11 : PS.State
closing11 = PS.supervising
  (GP.supervised (GP.Production.initial L.c41)
    (GP.Pool.poolState ((j₀ , (GP.Pool.deregisterPending GP.Pool.normalExit)) ∷ []) (j₀ ∷ []) nothing (GP.Pool.cancelPending j₀) (j₀ ∷ []) (j₀ ∷ []) [] (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
closing-step11 : PS.step (PS.run (GP.run L.a41)) closing10 ≡ just closing11
closing-step11 = refl
closing12 : PS.State
closing12 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.deregistered GP.Pool.normalExit)) ∷ []) [] nothing (GP.Pool.cancelPending j₀) (j₀ ∷ []) (j₀ ∷ []) [] (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
closing-step12 : PS.step (PS.run (GP.run L.a42)) closing11 ≡ just closing12
closing-step12 = refl
closing13 : PS.State
closing13 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing (GP.Pool.cancelPending j₀) (j₀ ∷ []) (j₀ ∷ []) [] (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
closing-step13 : PS.step (PS.run (GP.publishAsyncResult j₀)) closing12 ≡ just closing13
closing-step13 = refl
closing14 : PS.State
closing14 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closing (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
closing-step14 : PS.step (PS.run GP.join) closing13 ≡ just closing14
closing-step14 = refl
closing15 : PS.State
closing15 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
closing-step15 : PS.step (PS.run GP.finishClose) closing14 ≡ just closing15
closing-step15 = refl

-- A checked intermediate governor-pool close keeps the remaining physical
-- registry/scope acceptance layer independent of these elaboration contexts.
governorCloseActions : List PS.Action
governorCloseActions = (PS.scope Scope.beginUnwind) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.scope (Scope.bodyExit Scope.churn)) ∷ (PS.scope (Scope.publishResult Scope.churn)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.run (GP.beginClose (j₀ ∷ []))) ∷ (PS.run GP.requestCancel) ∷ (PS.run (GP.run L.a41)) ∷ (PS.run (GP.run L.a42)) ∷ (PS.run (GP.publishAsyncResult j₀)) ∷ (PS.run GP.join) ∷ (PS.run GP.finishClose) ∷ []
abstract
  governor-close-suffix : PS.Executes m4 governorCloseActions closing15
  governor-close-suffix = PS.next {s = m4} {s₁ = closing1} {s₂ = closing15} closing-step1 (PS.next {s = closing1} {s₁ = closing2} {s₂ = closing15} closing-step2 (PS.next {s = closing2} {s₁ = closing3} {s₂ = closing15} closing-step3 (PS.next {s = closing3} {s₁ = closing4} {s₂ = closing15} closing-step4 (PS.next {s = closing4} {s₁ = closing5} {s₂ = closing15} closing-step5 (PS.next {s = closing5} {s₁ = closing6} {s₂ = closing15} closing-step6 (PS.next {s = closing6} {s₁ = closing7} {s₂ = closing15} closing-step7 (PS.next {s = closing7} {s₁ = closing8} {s₂ = closing15} closing-step8 (PS.next {s = closing8} {s₁ = closing9} {s₂ = closing15} closing-step9 (PS.next {s = closing9} {s₁ = closing10} {s₂ = closing15} closing-step10 (PS.next {s = closing10} {s₁ = closing11} {s₂ = closing15} closing-step11 (PS.next {s = closing11} {s₁ = closing12} {s₂ = closing15} closing-step12 (PS.next {s = closing12} {s₁ = closing13} {s₂ = closing15} closing-step13 (PS.next {s = closing13} {s₁ = closing14} {s₂ = closing15} closing-step14 (PS.next {s = closing14} {s₁ = closing15} {s₂ = closing15} closing-step15 (PS.done)))))))))))))))
governor-close-checkpoint : GP.Pool.phase (GP.pool (PS.governor closing15)) ≡ GP.Pool.closedPool
governor-close-checkpoint = refl
