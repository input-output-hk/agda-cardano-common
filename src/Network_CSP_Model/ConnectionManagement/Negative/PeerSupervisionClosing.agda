{-# OPTIONS --guardedness #-}

-- Nonempty physical-registry closure, layered over checked scenario controls.
module ConnectionManagement.Negative.PeerSupervisionClosing where
open import ConnectionManagement.Negative.PeerSupervisionGovernorClose public
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Scenarios.Admission using (key₀)
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
closing16 : PS.State
closing16 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads8 (Scope.closing Scope.governor) true)
closing-step16 : PS.step (PS.scope (Scope.bodyExit Scope.governor)) closing15 ≡ just closing16
closing-step16 = refl
closing17 : PS.State
closing17 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads9 (Scope.closing Scope.governor) true)
closing-step17 : PS.step (PS.scope (Scope.publishResult Scope.governor)) closing16 ≡ just closing17
closing-step17 = refl
closing18 : PS.State
closing18 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads10 (Scope.closing Scope.localRoot) false)
closing-step18 : PS.step (PS.scope Scope.join) closing17 ≡ just closing18
closing-step18 = refl
closing19 : PS.State
closing19 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads11 (Scope.closing Scope.localRoot) true)
closing-step19 : PS.step (PS.scope Scope.requestCancel) closing18 ≡ just closing19
closing-step19 = refl
closing20 : PS.State
closing20 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads12 (Scope.closing Scope.localRoot) true)
closing-step20 : PS.step (PS.scope Scope.deliverCancel) closing19 ≡ just closing20
closing-step20 = refl
closing21 : PS.State
closing21 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads13 (Scope.closing Scope.localRoot) true)
closing-step21 : PS.step (PS.scope (Scope.bodyExit Scope.localRoot)) closing20 ≡ just closing21
closing-step21 = refl
closing22 : PS.State
closing22 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads14 (Scope.closing Scope.localRoot) true)
closing-step22 : PS.step (PS.scope (Scope.publishResult Scope.localRoot)) closing21 ≡ just closing22
closing-step22 = refl
closing23 : PS.State
closing23 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads15 (Scope.closing Scope.ledger) false)
closing-step23 : PS.step (PS.scope Scope.join) closing22 ≡ just closing23
closing-step23 = refl
closing24 : PS.State
closing24 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads16 (Scope.closing Scope.ledger) true)
closing-step24 : PS.step (PS.scope Scope.requestCancel) closing23 ≡ just closing24
closing-step24 = refl
closing25 : PS.State
closing25 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads17 (Scope.closing Scope.ledger) true)
closing-step25 : PS.step (PS.scope Scope.deliverCancel) closing24 ≡ just closing25
closing-step25 = refl
closing26 : PS.State
closing26 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads18 (Scope.closing Scope.ledger) true)
closing-step26 : PS.step (PS.scope (Scope.bodyExit Scope.ledger)) closing25 ≡ just closing26
closing-step26 = refl
closing27 : PS.State
closing27 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads19 (Scope.closing Scope.ledger) true)
closing-step27 : PS.step (PS.scope (Scope.publishResult Scope.ledger)) closing26 ≡ just closing27
closing-step27 = refl
closing28 : PS.State
closing28 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads20 Scope.readyToFinish false)
closing-step28 : PS.step (PS.scope Scope.join) closing27 ≡ just closing28
closing-step28 = refl
closing29 : PS.State
closing29 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.openPool [] [] [] [])
  (Scope.scopes scopeThreads20 Scope.finishedScope false)
closing-step29 : PS.step (PS.scope Scope.finishClose) closing28 ≡ just closing29
closing-step29 = refl
closing30 : PS.State
closing30 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing Pool.closing (tid₀ ∷ []) (tid₀ ∷ []) [] [])
  (Scope.scopes scopeThreads20 Scope.finishedScope false)
closing-step30 : PS.step (PS.beginMonitorClose (tid₀ ∷ [])) closing29 ≡ just closing30
closing-step30 = refl
closing31 : PS.State
closing31 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyRunning) ∷ []) (tid₀ ∷ []) nothing (Pool.cancelPending tid₀) (tid₀ ∷ []) (tid₀ ∷ []) [] [])
  (Scope.scopes scopeThreads20 Scope.finishedScope false)
closing-step31 : PS.step (PS.requestMonitorCancel) closing30 ≡ just closing31
closing-step31 = refl
closing32 : PS.State
closing32 = PS.supervising
  (GP.supervised (GP.Production.initial L.c42)
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.cancelling (just (Cancel.cancellation monitorWorker (errorId 9) Cancel.noCaller (Cancel.finished Cancel.abandoned)))) ∷ [])
  (Pool.poolState ((tid₀ , Pool.bodyUnwinding) ∷ []) (tid₀ ∷ []) nothing (Pool.joinPending tid₀) (tid₀ ∷ []) (tid₀ ∷ []) [] [])
  (Scope.scopes scopeThreads20 Scope.finishedScope false)
closing-step32 : PS.step (PS.deliverMonitorCancellation (errorId 9)) closing31 ≡ just closing32
closing-step32 = refl
closing33 : PS.State
closing33 = PS.supervising
  (GP.supervised (GP.Production.initial (record L.c42 { world = record (Sub.world L.c42) { peers = ((ident 0) , record L.p10 { monitorStarted = false }) ∷ [] } }))
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.exited (just (Cancel.cancellation monitorWorker (errorId 9) Cancel.noCaller (Cancel.finished Cancel.abandoned)))) ∷ [])
  (Pool.poolState ((tid₀ , (Pool.deregisterPending Pool.cancelledExit)) ∷ []) (tid₀ ∷ []) nothing (Pool.joinPending tid₀) (tid₀ ∷ []) (tid₀ ∷ []) [] [])
  (Scope.scopes scopeThreads20 Scope.finishedScope false)
closing-step33 : PS.step (PS.monitorBodyUnwound tid₀) closing32 ≡ just closing33
closing-step33 = refl
closing34 : PS.State
closing34 = PS.supervising
  (GP.supervised (GP.Production.initial (record L.c42 { world = record (Sub.world L.c42) { peers = ((ident 0) , record L.p10 { monitorStarted = false }) ∷ [] } }))
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.exited (just (Cancel.cancellation monitorWorker (errorId 9) Cancel.noCaller (Cancel.finished Cancel.abandoned)))) ∷ [])
  (Pool.poolState ((tid₀ , (Pool.deregistered Pool.cancelledExit)) ∷ []) [] nothing (Pool.joinPending tid₀) (tid₀ ∷ []) (tid₀ ∷ []) [] [])
  (Scope.scopes scopeThreads20 Scope.finishedScope false)
closing-step34 : PS.step (PS.deregisterMonitor tid₀) closing33 ≡ just closing34
closing-step34 = refl
closing35 : PS.State
closing35 = PS.supervising
  (GP.supervised (GP.Production.initial (record L.c42 { world = record (Sub.world L.c42) { peers = ((ident 0) , record L.p10 { monitorStarted = false }) ∷ [] } }))
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.exited (just (Cancel.cancellation monitorWorker (errorId 9) Cancel.noCaller (Cancel.finished Cancel.abandoned)))) ∷ [])
  (Pool.poolState ((tid₀ , (Pool.resultAvailable Pool.cancelledExit)) ∷ []) [] nothing (Pool.joinPending tid₀) (tid₀ ∷ []) (tid₀ ∷ []) [] [])
  (Scope.scopes scopeThreads20 Scope.finishedScope false)
closing-step35 : PS.step (PS.publishMonitorResult tid₀) closing34 ≡ just closing35
closing-step35 = refl
closing36 : PS.State
closing36 = PS.supervising
  (GP.supervised (GP.Production.initial (record L.c42 { world = record (Sub.world L.c42) { peers = ((ident 0) , record L.p10 { monitorStarted = false }) ∷ [] } }))
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.exited (just (Cancel.cancellation monitorWorker (errorId 9) Cancel.noCaller (Cancel.finished Cancel.abandoned)))) ∷ [])
  (Pool.poolState ((tid₀ , (Pool.resultAvailable Pool.cancelledExit)) ∷ []) [] nothing Pool.closing (tid₀ ∷ []) [] (tid₀ ∷ []) [])
  (Scope.scopes scopeThreads20 Scope.finishedScope false)
closing-step36 : PS.step (PS.joinMonitor) closing35 ≡ just closing36
closing-step36 = refl
closing37 : PS.State
closing37 = PS.supervising
  (GP.supervised (GP.Production.initial (record L.c42 { world = record (Sub.world L.c42) { peers = ((ident 0) , record L.p10 { monitorStarted = false }) ∷ [] } }))
    (GP.Pool.poolState ((j₀ , (GP.Pool.resultAvailable GP.Pool.normalExit)) ∷ []) [] nothing GP.Pool.closedPool (j₀ ∷ []) [] (j₀ ∷ []) (GP.body j₀ Prior.work (G.establishedOK (ident 0)) ∷ []))
    ((L.caller , Cancel.ordinary) ∷ []) [])
  ((tid₀ , physicalThread PS.returned PS.exited (just (Cancel.cancellation monitorWorker (errorId 9) Cancel.noCaller (Cancel.finished Cancel.abandoned)))) ∷ [])
  (Pool.poolState ((tid₀ , (Pool.resultAvailable Pool.cancelledExit)) ∷ []) [] nothing Pool.closedPool (tid₀ ∷ []) [] (tid₀ ∷ []) [])
  (Scope.scopes scopeThreads20 Scope.finishedScope false)
closing-step37 : PS.step (PS.finishMonitorClose) closing36 ≡ just closing37
closing-step37 = refl
-- Continue from the checked nonempty governor close checkpoint.
providerMonitorCloseActions : List PS.Action
providerMonitorCloseActions = (PS.scope (Scope.bodyExit Scope.governor)) ∷ (PS.scope (Scope.publishResult Scope.governor)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.scope (Scope.bodyExit Scope.localRoot)) ∷ (PS.scope (Scope.publishResult Scope.localRoot)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.scope (Scope.bodyExit Scope.ledger)) ∷ (PS.scope (Scope.publishResult Scope.ledger)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.finishClose) ∷ (PS.beginMonitorClose (tid₀ ∷ [])) ∷ (PS.requestMonitorCancel) ∷ (PS.deliverMonitorCancellation (errorId 9)) ∷ (PS.monitorBodyUnwound tid₀) ∷ (PS.deregisterMonitor tid₀) ∷ (PS.publishMonitorResult tid₀) ∷ (PS.joinMonitor) ∷ (PS.finishMonitorClose) ∷ []
abstract
  provider-monitor-close-suffix : PS.Executes closing15 providerMonitorCloseActions closing37
  provider-monitor-close-suffix = PS.next {s = closing15} {s₁ = closing16} {s₂ = closing37} closing-step16 (PS.next {s = closing16} {s₁ = closing17} {s₂ = closing37} closing-step17 (PS.next {s = closing17} {s₁ = closing18} {s₂ = closing37} closing-step18 (PS.next {s = closing18} {s₁ = closing19} {s₂ = closing37} closing-step19 (PS.next {s = closing19} {s₁ = closing20} {s₂ = closing37} closing-step20 (PS.next {s = closing20} {s₁ = closing21} {s₂ = closing37} closing-step21 (PS.next {s = closing21} {s₁ = closing22} {s₂ = closing37} closing-step22 (PS.next {s = closing22} {s₁ = closing23} {s₂ = closing37} closing-step23 (PS.next {s = closing23} {s₁ = closing24} {s₂ = closing37} closing-step24 (PS.next {s = closing24} {s₁ = closing25} {s₂ = closing37} closing-step25 (PS.next {s = closing25} {s₁ = closing26} {s₂ = closing37} closing-step26 (PS.next {s = closing26} {s₁ = closing27} {s₂ = closing37} closing-step27 (PS.next {s = closing27} {s₁ = closing28} {s₂ = closing37} closing-step28 (PS.next {s = closing28} {s₁ = closing29} {s₂ = closing37} closing-step29 (PS.next {s = closing29} {s₁ = closing30} {s₂ = closing37} closing-step30 (PS.next {s = closing30} {s₁ = closing31} {s₂ = closing37} closing-step31 (PS.next {s = closing31} {s₁ = closing32} {s₂ = closing37} closing-step32 (PS.next {s = closing32} {s₁ = closing33} {s₂ = closing37} closing-step33 (PS.next {s = closing33} {s₁ = closing34} {s₂ = closing37} closing-step34 (PS.next {s = closing34} {s₁ = closing35} {s₂ = closing37} closing-step35 (PS.next {s = closing35} {s₁ = closing36} {s₂ = closing37} closing-step36 (PS.next {s = closing36} {s₁ = closing37} {s₂ = closing37} closing-step37 (PS.done))))))))))))))))))))))

nonemptyCloseActions : List PS.Action
nonemptyCloseActions = (PS.scope Scope.beginUnwind) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.scope (Scope.bodyExit Scope.churn)) ∷ (PS.scope (Scope.publishResult Scope.churn)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.run (GP.beginClose (j₀ ∷ []))) ∷ (PS.run GP.requestCancel) ∷ (PS.run (GP.run L.a41)) ∷ (PS.run (GP.run L.a42)) ∷ (PS.run (GP.publishAsyncResult j₀)) ∷ (PS.run GP.join) ∷ (PS.run GP.finishClose) ∷ (PS.scope (Scope.bodyExit Scope.governor)) ∷ (PS.scope (Scope.publishResult Scope.governor)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.scope (Scope.bodyExit Scope.localRoot)) ∷ (PS.scope (Scope.publishResult Scope.localRoot)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.scope (Scope.bodyExit Scope.ledger)) ∷ (PS.scope (Scope.publishResult Scope.ledger)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.finishClose) ∷ (PS.beginMonitorClose (tid₀ ∷ [])) ∷ (PS.requestMonitorCancel) ∷ (PS.deliverMonitorCancellation (errorId 9)) ∷ (PS.monitorBodyUnwound tid₀) ∷ (PS.deregisterMonitor tid₀) ∷ (PS.publishMonitorResult tid₀) ∷ (PS.joinMonitor) ∷ (PS.finishMonitorClose) ∷ []
-- Keep checked execution evidence opaque to downstream certificate reduction.
abstract
  nonempty-close-suffix : PS.Executes m4 nonemptyCloseActions closing37
  nonempty-close-suffix = append governor-close-suffix provider-monitor-close-suffix
-- Keep checked execution evidence opaque to downstream certificate reduction.
abstract
  initialized-nonempty-close : PS.Executes p₀ ((sourcePrefix ++ spawnActions) ++ nonemptyCloseActions) closing37
  initialized-nonempty-close = append initialized-spawn nonempty-close-suffix

-- The certificates are nonvacuous: each snapshot contains the real child that
-- was created in the initialized execution, and each terminal result is joined.
import ConnectionManagement.Properties.PeerSupervision as Certificates
module Cert = Certificates Prior.classify
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
-- Keep checked execution evidence opaque to downstream certificate reduction.
abstract
  nonempty-close-certificates :
    (∀ j → j ∈ GP.Pool.snapshot (GP.pool (PS.governor closing37)) → Cert.GClose.Terminal (GP.pool (PS.governor closing37)) j) ×
    (∀ tid → tid ∈ Pool.snapshot (PS.monitorPool closing37) → Cert.BClose.Terminal (PS.monitorPool closing37) tid) ×
    ScopeFacts.AllJoined (PS.scopes closing37)
  nonempty-close-certificates = Cert.from-initial initialized-nonempty-close refl refl refl
actual-governor-child-terminal : Cert.GClose.Terminal (GP.pool (PS.governor closing37)) j₀
actual-governor-child-terminal = proj₁ nonempty-close-certificates j₀ (here refl)
actual-physical-monitor-terminal : Cert.BClose.Terminal (PS.monitorPool closing37) tid₀
actual-physical-monitor-terminal = proj₁ (proj₂ nonempty-close-certificates) tid₀ (here refl)
normal-result-survives-scope-cancellation : Sub.completions (PS.machine closing37) ≡
  G.completion Prior.work (G.establishedOK (ident 0)) 0 ∷ []
normal-result-survives-scope-cancellation = refl
physical-cancellation-has-no-result-publication : Pool.completions (PS.monitorPool closing37) ≡ []
physical-cancellation-has-no-result-publication = refl
-- Remaining CM/handler/server scopes are deliberately outside this certificate.
-- The initialized handler is still present, so this is no full shutdown claim.
handler-still-present-after-three-scope-close : lookup O.child (S.handlers (PS.shared closing37)) ≡
  just (S.handlerStart (ident 0) O.sock (ident 0) key₀)
handler-still-present-after-three-scope-close = refl
returned-governor-body-cannot-receive-async-cancel : PS.step
  (PS.run (GP.deliverCancellation (errorId 9))) closing10 ≡ nothing
returned-governor-body-cannot-receive-async-cancel = refl

-- The initialized source capture/supply invariant also survives physical spawn,
-- normal governor publication, Async scope joins and monitor cancellation.
import ConnectionManagement.Properties.PeerSupervisionSupply as SupplyProof
module Bounds = SupplyProof Prior.classify
spawn-supply-bounded : Bounds.Bounded m4
spawn-supply-bounded = Bounds.from-initial Prior.initial-bounds initialized-spawn
spawn-captures-valid : Bounds.Valid m4
spawn-captures-valid = Bounds.from-initial-valid Prior.initial-bounds initialized-spawn
nonempty-close-supply-bounded : Bounds.Bounded closing37
nonempty-close-supply-bounded = Bounds.from-initial Prior.initial-bounds initialized-nonempty-close
nonempty-close-captures-valid : Bounds.Valid closing37
nonempty-close-captures-valid = Bounds.from-initial-valid Prior.initial-bounds initialized-nonempty-close
