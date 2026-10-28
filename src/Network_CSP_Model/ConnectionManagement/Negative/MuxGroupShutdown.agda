{-# OPTIONS --guardedness #-}

-- Actual initialized group shutdown and distinct whole-pool close paths.
-- Explicit unwind/drain/trace inputs observe their local source boundaries.
-- No buffer release, CM cleanup, rethrow or parent Async result follows here.
module ConnectionManagement.Negative.MuxGroupShutdown where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (job; worker; mux)
open import ConnectionManagement.IGTypes using (clean; errored)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxResultMonitor as ResultMonitor
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Scenarios.Admission using (key₀)
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Negative.MuxResultMonitor as F
import ConnectionManagement.Negative.MuxProtocolJobs as Old
module W = Group F.bearerClosed
module M = ResultMonitor F.bearerClosed
module Pool = P.Pool
module U = P.U
module Startup = P.Startup
owner : WorkerId
owner = Old.owner
err : ErrorId
err = Old.err
wrap : M.State → W.State
wrap m = W.shutdownState m []
actual-initializer : W.initial (O.initial Old.F.start) ≡ just (wrap (F.wrap Old.b0))
actual-initializer = refl

-- This predicate excludes only body operations whose source eligibility is a
-- state-dependent guard. Setup/fork/registration prefixes use none of those.
prefixSafeP : P.Action → Bool
prefixSafeP (P.protocolReturned _) = false
prefixSafeP (P.commitClean _) = false
prefixSafeP (P.protocolException _ _) = false
prefixSafeP (P.returnProtocol _) = false
prefixSafeP _ = true
prefixSafe : M.Action → Bool
prefixSafe (M.run a) = prefixSafeP a
prefixSafe _ = true
prefixProtocol : ∀ a m → prefixSafeP a ≡ true → W.protocolAllowed a (wrap m) ≡ true
prefixProtocol (P.run (U.run a)) m eq = refl
prefixProtocol (P.run (U.negotiate w ps fl)) m eq = refl
prefixProtocol (P.run (U.allocateHandle w h mid)) m eq = refl
prefixProtocol (P.run (U.publishSuccess w)) m eq = refl
prefixProtocol (P.run (U.startupStep w a)) m eq = refl
prefixProtocol (P.forkResponder w j r) m eq = refl
prefixProtocol (P.forkInitiator w j r n) m eq = refl
prefixProtocol (P.registerProtocol j) m eq = refl
prefixProtocol (P.publishProtocol j) m eq = refl
prefixProtocol (P.deregisterProtocol j) m eq = refl
prefixProtocol (P.asyncProtocolResult j) m eq = refl
prefixProtocol (P.infrastructureReturn w r e) m eq = refl
prefixProtocol (P.publishInfra w r) m eq = refl
prefixProtocol (P.deregisterInfra w r) m eq = refl
prefixProtocol (P.asyncInfraResult w r) m eq = refl
prefixProtocol (P.control w a) m eq = refl
prefixProtocol (P.protocolReturned j) m ()
prefixProtocol (P.commitClean j) m ()
prefixProtocol (P.protocolException j e) m ()
prefixProtocol (P.returnProtocol j) m ()
prefixAllowed : ∀ a m → prefixSafe a ≡ true → W.delegateAllowed a (wrap m) ≡ true
prefixAllowed (M.run a) m eq = prefixProtocol a m eq
prefixAllowed (M.consume w) m eq = refl
prefixAllowed (M.handleSelected w) m eq = refl
prefixAllowed (M.sampleTracer w) m eq = refl
prefixAllowed (M.commitTracer w) m eq = refl
prefixAllowed (M.finishProtocolTrace w) m eq = refl
prefixAllowed (M.beginDead w) m eq = refl
prefixAllowed (M.finishDead w) m eq = refl
prefixAll : List M.Action → Bool
prefixAll [] = true
prefixAll (a ∷ rest) = prefixSafe a ∧ prefixAll rest
lift-step : ∀ a m {n} → prefixSafe a ≡ true → M.step a m ≡ just n → W.step (W.run a) (wrap m) ≡ just (wrap n)
lift-step a m safe advanced rewrite prefixAllowed a m safe | advanced = refl
lift-path : ∀ {m actions n} → M.Executes m actions n → prefixAll actions ≡ true →
  W.Executes (wrap m) (map W.run actions) (wrap n)
lift-path M.done eq = W.done
lift-path (M.next {s = m} {a = a} {as = rest} advanced path) eq with prefixSafe a in safe | prefixAll rest in tailSafe
... | true | true = W.next (lift-step a m safe advanced) (lift-path path tailSafe)
... | false | _ = case eq of λ ()
... | true | false = case eq of λ ()
abstract
  initialized-running : W.Executes (wrap (F.wrap Old.b0))
    (map W.run (map M.run Old.startActions ++ F.errorPrefixActions)) (wrap F.error7)
  initialized-running = lift-path F.initialized-error-prefix refl

normal0 : W.State
normal0 = wrap F.error7
normal1 : W.State
normal1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = (Mux.shutdown ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) [])
normal-edge1 : W.step (W.requestShutdown owner) normal0 ≡ just normal1
normal-edge1 = refl
normal2 : W.State
normal2 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = [] }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.shutdownSelected) [] [] [] (W.ready)) ∷ []))
normal-edge2 : W.step (W.selectShutdown owner) normal1 ≡ just normal2
normal-edge2 = refl
normal3 : W.State
normal3 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = [] }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.stoppingTraced) [] [] [] (W.ready)) ∷ []))
normal-edge3 : W.step (W.observeStoppingTrace owner) normal2 ≡ just normal3
normal-edge3 = refl
normal4 : W.State
normal4 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.stoppingWritten) [] [] [] (W.ready)) ∷ []))
normal-edge4 : W.step (W.writeStopping owner) normal3 ≡ just normal4
normal-edge4 = refl
normal5 : W.State
normal5 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.ready)) ∷ []))
normal-edge5 : W.step (W.captureGroup owner (Old.j₁₀ ∷ [])) normal4 ≡ just normal5
normal-edge5 = refl
normal6 : W.State
normal6 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.requested Old.j₁₀)) ∷ []))
normal-edge6 : W.step (W.requestGroupCancel owner) normal5 ≡ just normal6
normal-edge6 = refl
normal7 : W.State
normal7 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyUnwinding) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
normal-edge7 : W.step (W.deliverGroup owner) normal6 ≡ just normal7
normal-edge7 = refl
normal8 : W.State
normal8 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.cancelledExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
normal-edge8 : W.step (W.finishChildUnwind Old.j₁₀) normal7 ≡ just normal8
normal-edge8 = refl
normal9 : W.State
normal9 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
normal-edge9 : W.step (W.run (M.run (P.deregisterProtocol Old.j₁₀))) normal8 ≡ just normal9
normal-edge9 = refl
normal10 : W.State
normal10 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
normal-edge10 : W.step (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) normal9 ≡ just normal10
normal-edge10 = refl
normal11 : W.State
normal11 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge11 : W.step (W.joinGroup owner) normal10 ≡ just normal11
normal-edge11 = refl
normal12 : W.State
normal12 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.draining) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge12 : W.step (W.finishGroup owner) normal11 ≡ just normal12
normal-edge12 = refl
normal13 : W.State
normal13 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.drainReady) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge13 : W.step (W.drainEmpty owner) normal12 ≡ just normal13
normal-edge13 = refl
normal14 : W.State
normal14 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.stoppedTrace) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge14 : W.step (W.writeStopped owner) normal13 ≡ just normal14
normal-edge14 = refl
normal14a normal14b normal14c : W.State
normal14a = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; callback = Mux.readActive Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal14b = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal14c = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal15 : W.State
normal15 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.monitorReturnedNormal) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge15 : W.step (W.observeTraceStopped owner) normal14 ≡ just normal14a
normal-edge15 = refl
normal-edge15a : W.step (W.sampleStoppedTracer owner) normal14a ≡ just normal14b
normal-edge15a = refl
normal-edge15b : W.step (W.commitStoppedTracer owner) normal14b ≡ just normal14c
normal-edge15b = refl
normal-edge15c : W.step (W.finishStoppedTrace owner) normal14c ≡ just normal15
normal-edge15c = refl
normal16 : W.State
normal16 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.closing) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge16 : W.step (W.beginWholeClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) normal15 ≡ just normal16
normal-edge16 = refl
normal17 : W.State
normal17 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge17 : W.step (W.requestWholeCancel owner) normal16 ≡ just normal17
normal-edge17 = refl
normal18 : W.State
normal18 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyUnwinding) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge18 : W.step (W.deliverWhole owner) normal17 ≡ just normal18
normal-edge18 = refl
normal19 : W.State
normal19 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge19 : W.step (W.finishChildUnwind Old.j₁) normal18 ≡ just normal19
normal-edge19 = refl
normal20 : W.State
normal20 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregistered Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge20 : W.step (W.run (M.run (P.deregisterInfra owner T.demuxer))) normal19 ≡ just normal20
normal-edge20 = refl
normal21 : W.State
normal21 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge21 : W.step (W.run (M.run (P.asyncInfraResult owner T.demuxer))) normal20 ≡ just normal21
normal-edge21 = refl
normal22 : W.State
normal22 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.closing) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge22 : W.step (W.joinWhole owner) normal21 ≡ just normal22
normal-edge22 = refl
normal23 : W.State
normal23 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge23 : W.step (W.requestWholeCancel owner) normal22 ≡ just normal23
normal-edge23 = refl
normal24 : W.State
normal24 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyUnwinding) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge24 : W.step (W.deliverWhole owner) normal23 ≡ just normal24
normal-edge24 = refl
normal25 : W.State
normal25 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge25 : W.step (W.finishChildUnwind Old.j₀) normal24 ≡ just normal25
normal-edge25 = refl
normal26 : W.State
normal26 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.deregistered Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge26 : W.step (W.run (M.run (P.deregisterInfra owner T.muxer))) normal25 ≡ just normal26
normal-edge26 = refl
normal27 : W.State
normal27 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge27 : W.step (W.run (M.run (P.asyncInfraResult owner T.muxer))) normal26 ≡ just normal27
normal-edge27 = refl
normal28 : W.State
normal28 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closing) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge28 : W.step (W.joinWhole owner) normal27 ≡ just normal28
normal-edge28 = refl
normal29 : W.State
normal29 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosed W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge29 : W.step (W.finishWholeClose owner) normal28 ≡ just normal29
normal-edge29 = refl
normal30 : W.State
normal30 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.scopeDone W.normalExit) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
normal-edge30 : W.step (W.finishNormalScope owner) normal29 ≡ just normal30
normal-edge30 = refl
normalActions : List W.Action
normalActions = ((W.requestShutdown owner) ∷ (W.selectShutdown owner) ∷ (W.observeStoppingTrace owner) ∷ (W.writeStopping owner) ∷ (W.captureGroup owner (Old.j₁₀ ∷ [])) ∷ (W.requestGroupCancel owner) ∷ (W.deliverGroup owner) ∷ (W.finishChildUnwind Old.j₁₀) ∷ (W.run (M.run (P.deregisterProtocol Old.j₁₀))) ∷ (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) ∷ (W.joinGroup owner) ∷ (W.finishGroup owner) ∷ (W.drainEmpty owner) ∷ (W.writeStopped owner) ∷ (W.observeTraceStopped owner) ∷ W.sampleStoppedTracer owner ∷ W.commitStoppedTracer owner ∷ W.finishStoppedTrace owner ∷ (W.beginWholeClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) ∷ (W.requestWholeCancel owner) ∷ (W.deliverWhole owner) ∷ (W.finishChildUnwind Old.j₁) ∷ (W.run (M.run (P.deregisterInfra owner T.demuxer))) ∷ (W.run (M.run (P.asyncInfraResult owner T.demuxer))) ∷ (W.joinWhole owner) ∷ (W.requestWholeCancel owner) ∷ (W.deliverWhole owner) ∷ (W.finishChildUnwind Old.j₀) ∷ (W.run (M.run (P.deregisterInfra owner T.muxer))) ∷ (W.run (M.run (P.asyncInfraResult owner T.muxer))) ∷ (W.joinWhole owner) ∷ (W.finishWholeClose owner) ∷ (W.finishNormalScope owner) ∷ [])
normalPath : W.Executes normal0 normalActions normal30
normalPath = W.next normal-edge1 (W.next normal-edge2 (W.next normal-edge3 (W.next normal-edge4 (W.next normal-edge5 (W.next normal-edge6 (W.next normal-edge7 (W.next normal-edge8 (W.next normal-edge9 (W.next normal-edge10 (W.next normal-edge11 (W.next normal-edge12 (W.next normal-edge13 (W.next normal-edge14 (W.next normal-edge15 (W.next normal-edge15a (W.next normal-edge15b (W.next normal-edge15c (W.next normal-edge16 (W.next normal-edge17 (W.next normal-edge18 (W.next normal-edge19 (W.next normal-edge20 (W.next normal-edge21 (W.next normal-edge22 (W.next normal-edge23 (W.next normal-edge24 (W.next normal-edge25 (W.next normal-edge26 (W.next normal-edge27 (W.next normal-edge28 (W.next normal-edge29 (W.next normal-edge30 (W.done)))))))))))))))))))))))))))))))))

cleanSeed : W.State
cleanSeed = wrap F.race2
clean-seed-returned : W.step (W.run (M.run (P.protocolReturned Old.j₁₀))) (wrap F.error7) ≡ just (wrap F.race1)
clean-seed-returned = refl
clean-seed-committed : W.step (W.run (M.run (P.commitClean Old.j₁₀))) (wrap F.race1) ≡ just cleanSeed
clean-seed-committed = refl
cleanCancel0 : W.State
cleanCancel0 = cleanSeed
cleanCancel1 : W.State
cleanCancel1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); commands = (Mux.shutdown ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) [])
cleanCancel-edge1 : W.step (W.requestShutdown owner) cleanCancel0 ≡ just cleanCancel1
cleanCancel-edge1 = refl
cleanCancel2 : W.State
cleanCancel2 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); commands = [] }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.shutdownSelected) [] [] [] (W.ready)) ∷ []))
cleanCancel-edge2 : W.step (W.selectShutdown owner) cleanCancel1 ≡ just cleanCancel2
cleanCancel-edge2 = refl
cleanCancel3 : W.State
cleanCancel3 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); commands = [] }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.stoppingTraced) [] [] [] (W.ready)) ∷ []))
cleanCancel-edge3 : W.step (W.observeStoppingTrace owner) cleanCancel2 ≡ just cleanCancel3
cleanCancel-edge3 = refl
cleanCancel4 : W.State
cleanCancel4 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.stoppingWritten) [] [] [] (W.ready)) ∷ []))
cleanCancel-edge4 : W.step (W.writeStopping owner) cleanCancel3 ≡ just cleanCancel4
cleanCancel-edge4 = refl
cleanCancel5 : W.State
cleanCancel5 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.ready)) ∷ []))
cleanCancel-edge5 : W.step (W.captureGroup owner (Old.j₁₀ ∷ [])) cleanCancel4 ≡ just cleanCancel5
cleanCancel-edge5 = refl
cleanCancel6 : W.State
cleanCancel6 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.requested Old.j₁₀)) ∷ []))
cleanCancel-edge6 : W.step (W.requestGroupCancel owner) cleanCancel5 ≡ just cleanCancel6
cleanCancel-edge6 = refl
cleanCancel7 : W.State
cleanCancel7 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyUnwinding) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
cleanCancel-edge7 : W.step (W.deliverGroup owner) cleanCancel6 ≡ just cleanCancel7
cleanCancel-edge7 = refl
cleanCancel8 : W.State
cleanCancel8 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.cancelledExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
cleanCancel-edge8 : W.step (W.finishChildUnwind Old.j₁₀) cleanCancel7 ≡ just cleanCancel8
cleanCancel-edge8 = refl
cleanCancel9 : W.State
cleanCancel9 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
cleanCancel-edge9 : W.step (W.run (M.run (P.deregisterProtocol Old.j₁₀))) cleanCancel8 ≡ just cleanCancel9
cleanCancel-edge9 = refl
cleanCancel10 : W.State
cleanCancel10 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
cleanCancel-edge10 : W.step (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) cleanCancel9 ≡ just cleanCancel10
cleanCancel-edge10 = refl
cleanCancel11 : W.State
cleanCancel11 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
cleanCancel-edge11 : W.step (W.joinGroup owner) cleanCancel10 ≡ just cleanCancel11
cleanCancel-edge11 = refl
cleanCancel12 : W.State
cleanCancel12 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.draining) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
cleanCancel-edge12 : W.step (W.finishGroup owner) cleanCancel11 ≡ just cleanCancel12
cleanCancel-edge12 = refl
cleanCancel13 : W.State
cleanCancel13 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.drainReady) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
cleanCancel-edge13 : W.step (W.timeout2Elapsed owner) cleanCancel12 ≡ just cleanCancel13
cleanCancel-edge13 = refl
cleanCancel14 : W.State
cleanCancel14 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTrace) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
cleanCancel-edge14 : W.step (W.writeStopped owner) cleanCancel13 ≡ just cleanCancel14
cleanCancel-edge14 = refl
cleanCancel14a cleanCancel14b cleanCancel14c : W.State
cleanCancel14a = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopped; callback = Mux.readActive Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
cleanCancel14b = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
cleanCancel14c = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
cleanCancel15 : W.State
cleanCancel15 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); commands = []; status = Mux.stopped; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.monitorReturnedNormal) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
cleanCancel-edge15 : W.step (W.observeTraceStopped owner) cleanCancel14 ≡ just cleanCancel14a
cleanCancel-edge15 = refl
cleanCancel-edge15a : W.step (W.sampleStoppedTracer owner) cleanCancel14a ≡ just cleanCancel14b
cleanCancel-edge15a = refl
cleanCancel-edge15b : W.step (W.commitStoppedTracer owner) cleanCancel14b ≡ just cleanCancel14c
cleanCancel-edge15b = refl
cleanCancel-edge15c : W.step (W.finishStoppedTrace owner) cleanCancel14c ≡ just cleanCancel15
cleanCancel-edge15c = refl
cleanCancelActions : List W.Action
cleanCancelActions = ((W.requestShutdown owner) ∷ (W.selectShutdown owner) ∷ (W.observeStoppingTrace owner) ∷ (W.writeStopping owner) ∷ (W.captureGroup owner (Old.j₁₀ ∷ [])) ∷ (W.requestGroupCancel owner) ∷ (W.deliverGroup owner) ∷ (W.finishChildUnwind Old.j₁₀) ∷ (W.run (M.run (P.deregisterProtocol Old.j₁₀))) ∷ (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) ∷ (W.joinGroup owner) ∷ (W.finishGroup owner) ∷ (W.timeout2Elapsed owner) ∷ (W.writeStopped owner) ∷ (W.observeTraceStopped owner) ∷ W.sampleStoppedTracer owner ∷ W.commitStoppedTracer owner ∷ W.finishStoppedTrace owner ∷ [])
cleanCancelPath : W.Executes cleanCancel0 cleanCancelActions cleanCancel15
cleanCancelPath = W.next cleanCancel-edge1 (W.next cleanCancel-edge2 (W.next cleanCancel-edge3 (W.next cleanCancel-edge4 (W.next cleanCancel-edge5 (W.next cleanCancel-edge6 (W.next cleanCancel-edge7 (W.next cleanCancel-edge8 (W.next cleanCancel-edge9 (W.next cleanCancel-edge10 (W.next cleanCancel-edge11 (W.next cleanCancel-edge12 (W.next cleanCancel-edge13 (W.next cleanCancel-edge14 (W.next cleanCancel-edge15 (W.next cleanCancel-edge15a (W.next cleanCancel-edge15b (W.next cleanCancel-edge15c (W.done))))))))))))))))))

errorSeed : W.State
errorSeed = wrap F.errorTail1
error-seed-committed : W.step (W.run (M.run (P.protocolException Old.j₁₀ Old.err))) (wrap F.error7) ≡ just errorSeed
error-seed-committed = refl
errorOutruns0 : W.State
errorOutruns0 = errorSeed
errorOutruns1 : W.State
errorOutruns1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []); commands = (Mux.shutdown ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) [])
errorOutruns-edge1 : W.step (W.requestShutdown owner) errorOutruns0 ≡ just errorOutruns1
errorOutruns-edge1 = refl
errorOutruns2 : W.State
errorOutruns2 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []); commands = [] }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.shutdownSelected) [] [] [] (W.ready)) ∷ []))
errorOutruns-edge2 : W.step (W.selectShutdown owner) errorOutruns1 ≡ just errorOutruns2
errorOutruns-edge2 = refl
errorOutruns3 : W.State
errorOutruns3 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []); commands = [] }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.stoppingTraced) [] [] [] (W.ready)) ∷ []))
errorOutruns-edge3 : W.step (W.observeStoppingTrace owner) errorOutruns2 ≡ just errorOutruns3
errorOutruns-edge3 = refl
errorOutruns4 : W.State
errorOutruns4 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.stoppingWritten) [] [] [] (W.ready)) ∷ []))
errorOutruns-edge4 : W.step (W.writeStopping owner) errorOutruns3 ≡ just errorOutruns4
errorOutruns-edge4 = refl
errorOutruns5 : W.State
errorOutruns5 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.ready)) ∷ []))
errorOutruns-edge5 : W.step (W.captureGroup owner (Old.j₁₀ ∷ [])) errorOutruns4 ≡ just errorOutruns5
errorOutruns-edge5 = refl
errorOutruns6 : W.State
errorOutruns6 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.requested Old.j₁₀)) ∷ []))
errorOutruns-edge6 : W.step (W.requestGroupCancel owner) errorOutruns5 ≡ just errorOutruns6
errorOutruns-edge6 = refl
errorOutruns7 : W.State
errorOutruns7 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []); commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyReturned (T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err))) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.requested Old.j₁₀)) ∷ []))
errorOutruns-edge7 : W.step (W.run (M.run (P.returnProtocol Old.j₁₀))) errorOutruns6 ≡ just errorOutruns7
errorOutruns-edge7 = refl
errorOutruns8 : W.State
errorOutruns8 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopping; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.requested Old.j₁₀)) ∷ []))
errorOutruns-edge8 : W.step (W.run (M.run (P.publishProtocol Old.j₁₀))) errorOutruns7 ≡ just errorOutruns8
errorOutruns-edge8 = refl
errorOutruns9 : W.State
errorOutruns9 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopping; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.requested Old.j₁₀)) ∷ []))
errorOutruns-edge9 : W.step (W.run (M.run (P.deregisterProtocol Old.j₁₀))) errorOutruns8 ≡ just errorOutruns9
errorOutruns-edge9 = refl
errorOutruns10 : W.State
errorOutruns10 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopping; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.requested Old.j₁₀)) ∷ []))
errorOutruns-edge10 : W.step (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) errorOutruns9 ≡ just errorOutruns10
errorOutruns-edge10 = refl
errorOutruns11 : W.State
errorOutruns11 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopping; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
errorOutruns-edge11 : W.step (W.joinGroup owner) errorOutruns10 ≡ just errorOutruns11
errorOutruns-edge11 = refl
errorOutruns12 : W.State
errorOutruns12 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopping; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.draining) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
errorOutruns-edge12 : W.step (W.finishGroup owner) errorOutruns11 ≡ just errorOutruns12
errorOutruns-edge12 = refl
errorOutruns13 : W.State
errorOutruns13 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopping; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.drainReady) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
errorOutruns-edge13 : W.step (W.drainEmpty owner) errorOutruns12 ≡ just errorOutruns13
errorOutruns-edge13 = refl
errorOutruns14 : W.State
errorOutruns14 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopped; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTrace) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
errorOutruns-edge14 : W.step (W.writeStopped owner) errorOutruns13 ≡ just errorOutruns14
errorOutruns-edge14 = refl
errorOutruns14a errorOutruns14b errorOutruns14c : W.State
errorOutruns14a = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopped; callback = Mux.readActive Mux.muxStopped; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
errorOutruns14b = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
errorOutruns14c = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopped; traceCounters = nothing; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
errorOutruns15 : W.State
errorOutruns15 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; commands = []; status = Mux.stopped; traceCounters = nothing; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.monitorReturnedNormal) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
errorOutruns-edge15 : W.step (W.observeTraceStopped owner) errorOutruns14 ≡ just errorOutruns14a
errorOutruns-edge15 = refl
errorOutruns-edge15a : W.step (W.sampleStoppedTracer owner) errorOutruns14a ≡ just errorOutruns14b
errorOutruns-edge15a = refl
errorOutruns-edge15b : W.step (W.commitStoppedTracer owner) errorOutruns14b ≡ just errorOutruns14c
errorOutruns-edge15b = refl
errorOutruns-edge15c : W.step (W.finishStoppedTrace owner) errorOutruns14c ≡ just errorOutruns15
errorOutruns-edge15c = refl
errorOutrunsActions : List W.Action
errorOutrunsActions = ((W.requestShutdown owner) ∷ (W.selectShutdown owner) ∷ (W.observeStoppingTrace owner) ∷ (W.writeStopping owner) ∷ (W.captureGroup owner (Old.j₁₀ ∷ [])) ∷ (W.requestGroupCancel owner) ∷ (W.run (M.run (P.returnProtocol Old.j₁₀))) ∷ (W.run (M.run (P.publishProtocol Old.j₁₀))) ∷ (W.run (M.run (P.deregisterProtocol Old.j₁₀))) ∷ (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) ∷ (W.joinGroup owner) ∷ (W.finishGroup owner) ∷ (W.drainEmpty owner) ∷ (W.writeStopped owner) ∷ (W.observeTraceStopped owner) ∷ W.sampleStoppedTracer owner ∷ W.commitStoppedTracer owner ∷ W.finishStoppedTrace owner ∷ [])
errorOutrunsPath : W.Executes errorOutruns0 errorOutrunsActions errorOutruns15
errorOutrunsPath = W.next errorOutruns-edge1 (W.next errorOutruns-edge2 (W.next errorOutruns-edge3 (W.next errorOutruns-edge4 (W.next errorOutruns-edge5 (W.next errorOutruns-edge6 (W.next errorOutruns-edge7 (W.next errorOutruns-edge8 (W.next errorOutruns-edge9 (W.next errorOutruns-edge10 (W.next errorOutruns-edge11 (W.next errorOutruns-edge12 (W.next errorOutruns-edge13 (W.next errorOutruns-edge14 (W.next errorOutruns-edge15 (W.next errorOutruns-edge15a (W.next errorOutruns-edge15b (W.next errorOutruns-edge15c (W.done))))))))))))))))))

replacement0 : W.State
replacement0 = normal7
replacement1 : W.State
replacement1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping; runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
replacement-edge1 : W.step (W.unwindReplacedBySync Old.j₁₀ Old.err) replacement0 ≡ just replacement1
replacement-edge1 = refl
replacement2 : W.State
replacement2 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping; runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyReturned (T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err))) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
replacement-edge2 : W.step (W.run (M.run (P.returnProtocol Old.j₁₀))) replacement1 ≡ just replacement2
replacement-edge2 = refl
replacement3 : W.State
replacement3 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
replacement-edge3 : W.step (W.run (M.run (P.publishProtocol Old.j₁₀))) replacement2 ≡ just replacement3
replacement-edge3 = refl
replacement4 : W.State
replacement4 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
replacement-edge4 : W.step (W.run (M.run (P.deregisterProtocol Old.j₁₀))) replacement3 ≡ just replacement4
replacement-edge4 = refl
replacement5 : W.State
replacement5 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
replacement-edge5 : W.step (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) replacement4 ≡ just replacement5
replacement-edge5 = refl
replacement6 : W.State
replacement6 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
replacement-edge6 : W.step (W.joinGroup owner) replacement5 ≡ just replacement6
replacement-edge6 = refl
replacement7 : W.State
replacement7 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.draining) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
replacement-edge7 : W.step (W.finishGroup owner) replacement6 ≡ just replacement7
replacement-edge7 = refl
replacement8 : W.State
replacement8 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.drainReady) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
replacement-edge8 : W.step (W.drainEmpty owner) replacement7 ≡ just replacement8
replacement-edge8 = refl
replacement9 : W.State
replacement9 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTrace) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
replacement-edge9 : W.step (W.writeStopped owner) replacement8 ≡ just replacement9
replacement-edge9 = refl
replacement9a replacement9b replacement9c : W.State
replacement9a = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; callback = Mux.readActive Mux.muxStopped; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
replacement9b = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
replacement9c = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.stoppedTracing) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
replacement10 : W.State
replacement10 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing; runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) []) ((owner , W.frame (W.monitorReturnedNormal) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
replacement-edge10 : W.step (W.observeTraceStopped owner) replacement9 ≡ just replacement9a
replacement-edge10 = refl
replacement-edge10a : W.step (W.sampleStoppedTracer owner) replacement9a ≡ just replacement9b
replacement-edge10a = refl
replacement-edge10b : W.step (W.commitStoppedTracer owner) replacement9b ≡ just replacement9c
replacement-edge10b = refl
replacement-edge10c : W.step (W.finishStoppedTrace owner) replacement9c ≡ just replacement10
replacement-edge10c = refl
replacementActions : List W.Action
replacementActions = ((W.unwindReplacedBySync Old.j₁₀ Old.err) ∷ (W.run (M.run (P.returnProtocol Old.j₁₀))) ∷ (W.run (M.run (P.publishProtocol Old.j₁₀))) ∷ (W.run (M.run (P.deregisterProtocol Old.j₁₀))) ∷ (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) ∷ (W.joinGroup owner) ∷ (W.finishGroup owner) ∷ (W.drainEmpty owner) ∷ (W.writeStopped owner) ∷ (W.observeTraceStopped owner) ∷ W.sampleStoppedTracer owner ∷ W.commitStoppedTracer owner ∷ W.finishStoppedTrace owner ∷ [])
replacementPath : W.Executes replacement0 replacementActions replacement10
replacementPath = W.next replacement-edge1 (W.next replacement-edge2 (W.next replacement-edge3 (W.next replacement-edge4 (W.next replacement-edge5 (W.next replacement-edge6 (W.next replacement-edge7 (W.next replacement-edge8 (W.next replacement-edge9 (W.next replacement-edge10 (W.next replacement-edge10a (W.next replacement-edge10b (W.next replacement-edge10c (W.done)))))))))))))

engineDuringGroup0 : W.State
engineDuringGroup0 = normal7
engineDuringGroup1 : W.State
engineDuringGroup1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyReturned (T.infraMuxer Old.err)) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyUnwinding) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
engineDuringGroup-edge1 : W.step (W.run (M.run (P.infrastructureReturn owner T.muxer Old.err))) engineDuringGroup0 ≡ just engineDuringGroup1
engineDuringGroup-edge1 = refl
engineDuringGroup2 : W.State
engineDuringGroup2 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyUnwinding) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.infraMuxer Old.err) ∷ [])) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.groupClosing) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
engineDuringGroup-edge2 : W.step (W.run (M.run (P.publishInfra owner T.muxer))) engineDuringGroup1 ≡ just engineDuringGroup2
engineDuringGroup-edge2 = refl
engineDuringGroupActions : List W.Action
engineDuringGroupActions = ((W.run (M.run (P.infrastructureReturn owner T.muxer Old.err))) ∷ (W.run (M.run (P.publishInfra owner T.muxer))) ∷ [])
engineDuringGroupPath : W.Executes engineDuringGroup0 engineDuringGroupActions engineDuringGroup2
engineDuringGroupPath = W.next engineDuringGroup-edge1 (W.next engineDuringGroup-edge2 (W.done))

abortGroup0 : W.State
abortGroup0 = normal7
abortGroup1 : W.State
abortGroup1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyUnwinding) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.ownerAborting Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge1 : W.step (W.abortOwner owner Old.err) abortGroup0 ≡ just abortGroup1
abortGroup-edge1 = refl
abortGroup2 : W.State
abortGroup2 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyUnwinding) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.closing) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge2 : W.step (W.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ [])) abortGroup1 ≡ just abortGroup2
abortGroup-edge2 = refl
abortGroup3 : W.State
abortGroup3 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyUnwinding) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₁₀) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge3 : W.step (W.requestWholeCancel owner) abortGroup2 ≡ just abortGroup3
abortGroup-edge3 = refl
abortGroup4 : W.State
abortGroup4 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.cancelledExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₁₀) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge4 : W.step (W.finishChildUnwind Old.j₁₀) abortGroup3 ≡ just abortGroup4
abortGroup-edge4 = refl
abortGroup5 : W.State
abortGroup5 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₁₀) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge5 : W.step (W.run (M.run (P.deregisterProtocol Old.j₁₀))) abortGroup4 ≡ just abortGroup5
abortGroup-edge5 = refl
abortGroup6 : W.State
abortGroup6 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₁₀) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge6 : W.step (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) abortGroup5 ≡ just abortGroup6
abortGroup-edge6 = refl
abortGroup7 : W.State
abortGroup7 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.closing) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge7 : W.step (W.joinWhole owner) abortGroup6 ≡ just abortGroup7
abortGroup-edge7 = refl
abortGroup8 : W.State
abortGroup8 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₁) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge8 : W.step (W.requestWholeCancel owner) abortGroup7 ≡ just abortGroup8
abortGroup-edge8 = refl
abortGroup9 : W.State
abortGroup9 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyUnwinding) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge9 : W.step (W.deliverWhole owner) abortGroup8 ≡ just abortGroup9
abortGroup-edge9 = refl
abortGroup10 : W.State
abortGroup10 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge10 : W.step (W.finishChildUnwind Old.j₁) abortGroup9 ≡ just abortGroup10
abortGroup-edge10 = refl
abortGroup11 : W.State
abortGroup11 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregistered Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge11 : W.step (W.run (M.run (P.deregisterInfra owner T.demuxer))) abortGroup10 ≡ just abortGroup11
abortGroup-edge11 = refl
abortGroup12 : W.State
abortGroup12 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge12 : W.step (W.run (M.run (P.asyncInfraResult owner T.demuxer))) abortGroup11 ≡ just abortGroup12
abortGroup-edge12 = refl
abortGroup13 : W.State
abortGroup13 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.closing) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge13 : W.step (W.joinWhole owner) abortGroup12 ≡ just abortGroup13
abortGroup-edge13 = refl
abortGroup14 : W.State
abortGroup14 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₀) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge14 : W.step (W.requestWholeCancel owner) abortGroup13 ≡ just abortGroup14
abortGroup-edge14 = refl
abortGroup15 : W.State
abortGroup15 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyUnwinding) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₀) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge15 : W.step (W.deliverWhole owner) abortGroup14 ≡ just abortGroup15
abortGroup-edge15 = refl
abortGroup16 : W.State
abortGroup16 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₀) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge16 : W.step (W.finishChildUnwind Old.j₀) abortGroup15 ≡ just abortGroup16
abortGroup-edge16 = refl
abortGroup17 : W.State
abortGroup17 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.deregistered Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.joinPending Old.j₀) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge17 : W.step (W.run (M.run (P.deregisterInfra owner T.muxer))) abortGroup16 ≡ just abortGroup17
abortGroup-edge17 = refl
abortGroup18 : W.State
abortGroup18 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.joinPending Old.j₀) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge18 : W.step (W.run (M.run (P.asyncInfraResult owner T.muxer))) abortGroup17 ≡ just abortGroup18
abortGroup-edge18 = refl
abortGroup19 : W.State
abortGroup19 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closing) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge19 : W.step (W.joinWhole owner) abortGroup18 ≡ just abortGroup19
abortGroup-edge19 = refl
abortGroup20 : W.State
abortGroup20 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosed (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge20 : W.step (W.finishWholeClose owner) abortGroup19 ≡ just abortGroup20
abortGroup-edge20 = refl
abortGroup21 : W.State
abortGroup21 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.asyncFailureWritten Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge21 : W.step (W.writeAsyncFailure owner) abortGroup20 ≡ just abortGroup21
abortGroup-edge21 = refl
abortGroup22 : W.State
abortGroup22 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err; callback = Mux.readActive Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.asyncDeadTracing Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge22 : W.step (W.beginAsyncDead owner) abortGroup21 ≡ just abortGroup22
abortGroup-edge22 = refl
abortGroup23 : W.State
abortGroup23 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.asyncDeadTracing Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge23 : W.step (W.sampleAsyncTracer owner) abortGroup22 ≡ just abortGroup23
abortGroup-edge23 = refl
abortGroup24 : W.State
abortGroup24 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.asyncDeadTracing Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge24 : W.step (W.commitAsyncTracer owner) abortGroup23 ≡ just abortGroup24
abortGroup-edge24 = refl
abortGroup25 : W.State
abortGroup25 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.scopeDone (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
abortGroup-edge25 : W.step (W.finishAsyncDead owner) abortGroup24 ≡ just abortGroup25
abortGroup-edge25 = refl
abortGroupActions : List W.Action
abortGroupActions = ((W.abortOwner owner Old.err) ∷ (W.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ [])) ∷ (W.requestWholeCancel owner) ∷ (W.finishChildUnwind Old.j₁₀) ∷ (W.run (M.run (P.deregisterProtocol Old.j₁₀))) ∷ (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) ∷ (W.joinWhole owner) ∷ (W.requestWholeCancel owner) ∷ (W.deliverWhole owner) ∷ (W.finishChildUnwind Old.j₁) ∷ (W.run (M.run (P.deregisterInfra owner T.demuxer))) ∷ (W.run (M.run (P.asyncInfraResult owner T.demuxer))) ∷ (W.joinWhole owner) ∷ (W.requestWholeCancel owner) ∷ (W.deliverWhole owner) ∷ (W.finishChildUnwind Old.j₀) ∷ (W.run (M.run (P.deregisterInfra owner T.muxer))) ∷ (W.run (M.run (P.asyncInfraResult owner T.muxer))) ∷ (W.joinWhole owner) ∷ (W.finishWholeClose owner) ∷ (W.writeAsyncFailure owner) ∷ (W.beginAsyncDead owner) ∷ (W.sampleAsyncTracer owner) ∷ (W.commitAsyncTracer owner) ∷ (W.finishAsyncDead owner) ∷ [])
abortGroupPath : W.Executes abortGroup0 abortGroupActions abortGroup25
abortGroupPath = W.next abortGroup-edge1 (W.next abortGroup-edge2 (W.next abortGroup-edge3 (W.next abortGroup-edge4 (W.next abortGroup-edge5 (W.next abortGroup-edge6 (W.next abortGroup-edge7 (W.next abortGroup-edge8 (W.next abortGroup-edge9 (W.next abortGroup-edge10 (W.next abortGroup-edge11 (W.next abortGroup-edge12 (W.next abortGroup-edge13 (W.next abortGroup-edge14 (W.next abortGroup-edge15 (W.next abortGroup-edge16 (W.next abortGroup-edge17 (W.next abortGroup-edge18 (W.next abortGroup-edge19 (W.next abortGroup-edge20 (W.next abortGroup-edge21 (W.next abortGroup-edge22 (W.next abortGroup-edge23 (W.next abortGroup-edge24 (W.next abortGroup-edge25 (W.done)))))))))))))))))))))))))

removedAbort0 : W.State
removedAbort0 = normal9
removedAbort1 : W.State
removedAbort1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.ownerAborting Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge1 : W.step (W.abortOwner owner Old.err) removedAbort0 ≡ just removedAbort1
removedAbort-edge1 = refl
removedAbort2 : W.State
removedAbort2 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.closing) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge2 : W.step (W.beginWholeClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) removedAbort1 ≡ just removedAbort2
removedAbort-edge2 = refl
removedAbort3 : W.State
removedAbort3 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge3 : W.step (W.requestWholeCancel owner) removedAbort2 ≡ just removedAbort3
removedAbort-edge3 = refl
removedAbort4 : W.State
removedAbort4 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyUnwinding) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge4 : W.step (W.deliverWhole owner) removedAbort3 ≡ just removedAbort4
removedAbort-edge4 = refl
removedAbort5 : W.State
removedAbort5 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge5 : W.step (W.finishChildUnwind Old.j₁) removedAbort4 ≡ just removedAbort5
removedAbort-edge5 = refl
removedAbort6 : W.State
removedAbort6 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregistered Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge6 : W.step (W.run (M.run (P.deregisterInfra owner T.demuxer))) removedAbort5 ≡ just removedAbort6
removedAbort-edge6 = refl
removedAbort7 : W.State
removedAbort7 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge7 : W.step (W.run (M.run (P.asyncInfraResult owner T.demuxer))) removedAbort6 ≡ just removedAbort7
removedAbort-edge7 = refl
removedAbort8 : W.State
removedAbort8 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.closing) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge8 : W.step (W.joinWhole owner) removedAbort7 ≡ just removedAbort8
removedAbort-edge8 = refl
removedAbort9 : W.State
removedAbort9 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.cancelPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge9 : W.step (W.requestWholeCancel owner) removedAbort8 ≡ just removedAbort9
removedAbort-edge9 = refl
removedAbort10 : W.State
removedAbort10 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyUnwinding) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge10 : W.step (W.deliverWhole owner) removedAbort9 ≡ just removedAbort10
removedAbort-edge10 = refl
removedAbort11 : W.State
removedAbort11 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) (nothing) (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge11 : W.step (W.finishChildUnwind Old.j₀) removedAbort10 ≡ just removedAbort11
removedAbort-edge11 = refl
removedAbort12 : W.State
removedAbort12 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.deregistered Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) [] (nothing) (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge12 : W.step (W.run (M.run (P.deregisterInfra owner T.muxer))) removedAbort11 ≡ just removedAbort12
removedAbort-edge12 = refl
removedAbort13 : W.State
removedAbort13 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) [] (nothing) (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge13 : W.step (W.run (M.run (P.asyncInfraResult owner T.muxer))) removedAbort12 ≡ just removedAbort13
removedAbort-edge13 = refl
removedAbort14 : W.State
removedAbort14 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closing) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosing (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge14 : W.step (W.joinWhole owner) removedAbort13 ≡ just removedAbort14
removedAbort-edge14 = refl
removedAbort15 : W.State
removedAbort15 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.wholeClosed (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge15 : W.step (W.finishWholeClose owner) removedAbort14 ≡ just removedAbort15
removedAbort-edge15 = refl
removedAbort16 : W.State
removedAbort16 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.asyncFailureWritten Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge16 : W.step (W.writeAsyncFailure owner) removedAbort15 ≡ just removedAbort16
removedAbort-edge16 = refl
removedAbort17 : W.State
removedAbort17 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err; callback = Mux.readActive Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.asyncDeadTracing Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge17 : W.step (W.beginAsyncDead owner) removedAbort16 ≡ just removedAbort17
removedAbort-edge17 = refl
removedAbort18 : W.State
removedAbort18 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.asyncDeadTracing Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge18 : W.step (W.sampleAsyncTracer owner) removedAbort17 ≡ just removedAbort18
removedAbort-edge18 = refl
removedAbort19 : W.State
removedAbort19 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.asyncDeadTracing Old.err) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge19 : W.step (W.commitAsyncTracer owner) removedAbort18 ≡ just removedAbort19
removedAbort-edge19 = refl
removedAbort20 : W.State
removedAbort20 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.failed Old.err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ []))) (Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.cancelledExit) ∷ []) [] (nothing) (Pool.closedPool) (Old.j₁ ∷ Old.j₀ ∷ []) [] (Old.j₁ ∷ Old.j₀ ∷ []) []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.scopeDone (W.asyncExit Old.err)) (Old.j₁₀ ∷ []) (Old.j₁₀ ∷ []) [] (W.delivered Old.j₁₀)) ∷ []))
removedAbort-edge20 : W.step (W.finishAsyncDead owner) removedAbort19 ≡ just removedAbort20
removedAbort-edge20 = refl
removedAbortActions : List W.Action
removedAbortActions = ((W.abortOwner owner Old.err) ∷ (W.beginWholeClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) ∷ (W.requestWholeCancel owner) ∷ (W.deliverWhole owner) ∷ (W.finishChildUnwind Old.j₁) ∷ (W.run (M.run (P.deregisterInfra owner T.demuxer))) ∷ (W.run (M.run (P.asyncInfraResult owner T.demuxer))) ∷ (W.joinWhole owner) ∷ (W.requestWholeCancel owner) ∷ (W.deliverWhole owner) ∷ (W.finishChildUnwind Old.j₀) ∷ (W.run (M.run (P.deregisterInfra owner T.muxer))) ∷ (W.run (M.run (P.asyncInfraResult owner T.muxer))) ∷ (W.joinWhole owner) ∷ (W.finishWholeClose owner) ∷ (W.writeAsyncFailure owner) ∷ (W.beginAsyncDead owner) ∷ (W.sampleAsyncTracer owner) ∷ (W.commitAsyncTracer owner) ∷ (W.finishAsyncDead owner) ∷ [])
removedAbortPath : W.Executes removedAbort0 removedAbortActions removedAbort20
removedAbortPath = W.next removedAbort-edge1 (W.next removedAbort-edge2 (W.next removedAbort-edge3 (W.next removedAbort-edge4 (W.next removedAbort-edge5 (W.next removedAbort-edge6 (W.next removedAbort-edge7 (W.next removedAbort-edge8 (W.next removedAbort-edge9 (W.next removedAbort-edge10 (W.next removedAbort-edge11 (W.next removedAbort-edge12 (W.next removedAbort-edge13 (W.next removedAbort-edge14 (W.next removedAbort-edge15 (W.next removedAbort-edge16 (W.next removedAbort-edge17 (W.next removedAbort-edge18 (W.next removedAbort-edge19 (W.next removedAbort-edge20 (W.done))))))))))))))))))))

abortDrain0 : W.State
abortDrain0 = normal12
abortDrain1 : W.State
abortDrain1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = []; status = Mux.stopping }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) ((owner , W.frame (W.ownerAborting Old.err) (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) (W.ready)) ∷ []))
abortDrain-edge1 : W.step (W.abortOwner owner Old.err) abortDrain0 ≡ just abortDrain1
abortDrain-edge1 = refl
abortDrainActions : List W.Action
abortDrainActions = ((W.abortOwner owner Old.err) ∷ [])
abortDrainPath : W.Executes abortDrain0 abortDrainActions abortDrain1
abortDrainPath = W.next abortDrain-edge1 (W.done)

no-group-infrastructure : W.snapshot (W.frameAt owner normal5) ≡ Old.j₁₀ ∷ []
no-group-infrastructure = refl
async-cancel-keeps-source-running-status : P.muxAt Old.mid (W.protocolState normal8) ≡ just
  (record Old.m6 { status = Mux.stopping })
async-cancel-keeps-source-running-status = refl
async-cancel-produces-no-typed-result : Pool.completions (W.poolAt owner normal10) ≡ []
async-cancel-produces-no-typed-result = refl
-- TraceStopped has a real IG effect while retaining the graceful Stopped status.
graceful-TraceStopped-status : P.muxAt Old.mid (W.protocolState normal15) ≡ just
  (record Old.m6 { commands = []; status = Mux.stopped; traceCounters = nothing })
graceful-TraceStopped-status = refl
graceful-TraceStopped-publishes-finished : Shared.inboundInfo (Machine.world (O.core (W.source normal15))) ≡
  Old.messages ++ (Shared.muxFinished key₀ ∷ [])
graceful-TraceStopped-publishes-finished = refl
group-finished-pool-still-open : Pool.phase (W.poolAt owner normal15) ≡ Pool.openPool
group-finished-pool-still-open = refl
clean-cancel-preserves-Idle-and-drops-pending : P.muxAt Old.mid (W.protocolState cleanCancel8) ≡ just
  (record Old.cleanMux { status = Mux.stopping; finishedJobs = [] })
clean-cancel-preserves-Idle-and-drops-pending = refl
clean-cancel-retains-committed-metadata : lookup Old.j₁₀ (P.jobs (W.protocolState cleanCancel8)) ≡ just (Old.rJob (T.resultCaptured clean))
clean-cancel-retains-committed-metadata = refl
clean-cancel-no-error-queue : Pool.completions (W.poolAt owner cleanCancel8) ≡ []
clean-cancel-no-error-queue = refl
error-captured-refuses-async-delivery : W.step (W.deliverGroup owner) errorOutruns6 ≡ nothing
error-captured-refuses-async-delivery = refl
ordinary-handler-can-outrun-cancel : Pool.completions (W.poolAt owner errorOutruns10) ≡
  T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err) ∷ []
ordinary-handler-can-outrun-cancel = refl
no-fake-ordinary-error-on-delivery : W.step (W.run (M.run (P.protocolException Old.j₁₀ Old.err))) normal7 ≡ nothing
no-fake-ordinary-error-on-delivery = refl
replacement-is-explicit-before-error-result : Pool.completions (W.poolAt owner replacement3) ≡
  T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err) ∷ []
replacement-is-explicit-before-error-result = refl
engine-result-does-not-advance-group : W.remaining (W.frameAt owner engineDuringGroup2) ≡ Old.j₁₀ ∷ []
engine-result-does-not-advance-group = refl
engine-result-can-queue-during-group : Pool.completions (W.poolAt owner engineDuringGroup2) ≡ T.infraMuxer Old.err ∷ []
engine-result-can-queue-during-group = refl
abort-seals-group-cursor : W.step (W.joinGroup owner) abortGroup1 ≡ nothing
abort-seals-group-cursor = refl
abort-cannot-write-Failed-before-whole-close : W.step (W.writeAsyncFailure owner) abortGroup1 ≡ nothing
abort-cannot-write-Failed-before-whole-close = refl
abort-preserves-Stopping : P.muxAt Old.mid (W.protocolState abortGroup1) ≡ just
  (record Old.m6 { status = Mux.stopping })
abort-preserves-Stopping = refl
abandoned-group-not-joined-by-whole-close : W.joined (W.frameAt owner abortGroup25) ≡ []
abandoned-group-not-joined-by-whole-close = refl
removed-history-not-whole-snapshot : Pool.snapshot (W.poolAt owner removedAbort2) ≡ Old.j₁ ∷ Old.j₀ ∷ []
removed-history-not-whole-snapshot = refl
removed-history-still-no-Async-result : lookup Old.j₁₀ (Pool.handles (W.poolAt owner removedAbort20)) ≡ just (Pool.deregistered Pool.cancelledExit)
removed-history-still-no-Async-result = refl
drain-abort-cannot-resume-normal-path : W.step (W.drainEmpty owner) abortDrain1 ≡ nothing
drain-abort-cannot-resume-normal-path = refl
partial-group-is-not-pool-closed : Pool.phase (W.poolAt owner abortGroup1) ≡ Pool.openPool
partial-group-is-not-pool-closed = refl
priority0 : W.State
priority0 = wrap F.error7
priority1 : W.State
priority1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyReturned (T.infraMuxer Old.err)) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) [])
priority-edge1 : W.step (W.run (M.run (P.infrastructureReturn owner T.muxer Old.err))) priority0 ≡ just priority1
priority-edge1 = refl
priority2 : W.State
priority2 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.infraMuxer Old.err) ∷ [])) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) [])
priority-edge2 : W.step (W.run (M.run (P.publishInfra owner T.muxer))) priority1 ≡ just priority2
priority-edge2 = refl
priority3 : W.State
priority3 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = (Mux.shutdown ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (nothing) (Pool.openPool) [] [] [] ((T.infraMuxer Old.err) ∷ [])) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) [])
priority-edge3 : W.step (W.requestShutdown owner) priority2 ≡ just priority3
priority-edge3 = refl
priorityActions : List W.Action
priorityActions = ((W.run (M.run (P.infrastructureReturn owner T.muxer Old.err))) ∷ (W.run (M.run (P.publishInfra owner T.muxer))) ∷ (W.requestShutdown owner) ∷ [])
priorityPath : W.Executes priority0 priorityActions priority3
priorityPath = W.next priority-edge1 (W.next priority-edge2 (W.next priority-edge3 (W.done)))

forkGap0 : W.State
forkGap0 = wrap (F.wrap Old.r6)
forkGap1 : W.State
forkGap1 = (W.shutdownState (M.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { commands = (Mux.shutdown ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) (just Old.j₁₀) (Pool.openPool) [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) []) [])
forkGap-edge1 : W.step (W.requestShutdown owner) forkGap0 ≡ just forkGap1
forkGap-edge1 = refl
forkGapActions : List W.Action
forkGapActions = ((W.requestShutdown owner) ∷ [])
forkGapPath : W.Executes forkGap0 forkGapActions forkGap1
forkGapPath = W.next forkGap-edge1 (W.done)

physical-FIFO-blocks-shutdown-selection : W.step (W.selectShutdown owner) priority3 ≡ nothing
physical-FIFO-blocks-shutdown-selection = refl
masked-parent-insertion-blocks-shutdown-selection : W.step (W.selectShutdown owner) forkGap1 ≡ nothing
masked-parent-insertion-blocks-shutdown-selection = refl

-- A stop request can be made on a published handle before buffer/pool startup.
-- This is proved from the actual acquisition/handshake publication prefix.
withMux : Mux.Mux → O.Configuration → O.Configuration
withMux m c = record c { core = record (O.core c)
  { inboundGovernor = IG.setMux Old.mid m (Machine.inboundGovernor (O.core c)) } }
early0 earlyRequested : W.State
early0 = wrap (F.wrap Old.b15)
earlyRequested = W.setSource (withMux (record Old.G.newMux { commands = Mux.shutdown ∷ [] }) (W.source early0)) early0
stop-request-before-physical-startup : W.step (W.requestShutdown owner) early0 ≡ just earlyRequested
stop-request-before-physical-startup = refl
prestartup-request-does-not-create-pool : W.poolAt owner earlyRequested ≡ Pool.initial
prestartup-request-does-not-create-pool = refl
prestartup-request-cannot-select-monitor-command : W.step (W.selectShutdown owner) earlyRequested ≡ nothing
prestartup-request-cannot-select-monitor-command = refl
append : ∀ {s as t bs u} → W.Executes s as t → W.Executes t bs u → W.Executes s (as ++ bs) u
append W.done tail = tail
append (W.next eq path) tail = W.next eq (append path tail)
normalPrefix7Actions : List W.Action
normalPrefix7Actions = ((W.requestShutdown owner) ∷ (W.selectShutdown owner) ∷ (W.observeStoppingTrace owner) ∷ (W.writeStopping owner) ∷ (W.captureGroup owner (Old.j₁₀ ∷ [])) ∷ (W.requestGroupCancel owner) ∷ (W.deliverGroup owner) ∷ [])
normalPrefix7 : W.Executes normal0 normalPrefix7Actions normal7
normalPrefix7 = W.next normal-edge1 (W.next normal-edge2 (W.next normal-edge3 (W.next normal-edge4 (W.next normal-edge5 (W.next normal-edge6 (W.next normal-edge7 (W.done)))))))
normalPrefix9Actions : List W.Action
normalPrefix9Actions = ((W.requestShutdown owner) ∷ (W.selectShutdown owner) ∷ (W.observeStoppingTrace owner) ∷ (W.writeStopping owner) ∷ (W.captureGroup owner (Old.j₁₀ ∷ [])) ∷ (W.requestGroupCancel owner) ∷ (W.deliverGroup owner) ∷ (W.finishChildUnwind Old.j₁₀) ∷ (W.run (M.run (P.deregisterProtocol Old.j₁₀))) ∷ [])
normalPrefix9 : W.Executes normal0 normalPrefix9Actions normal9
normalPrefix9 = W.next normal-edge1 (W.next normal-edge2 (W.next normal-edge3 (W.next normal-edge4 (W.next normal-edge5 (W.next normal-edge6 (W.next normal-edge7 (W.next normal-edge8 (W.next normal-edge9 (W.done)))))))))
normalPrefix12Actions : List W.Action
normalPrefix12Actions = ((W.requestShutdown owner) ∷ (W.selectShutdown owner) ∷ (W.observeStoppingTrace owner) ∷ (W.writeStopping owner) ∷ (W.captureGroup owner (Old.j₁₀ ∷ [])) ∷ (W.requestGroupCancel owner) ∷ (W.deliverGroup owner) ∷ (W.finishChildUnwind Old.j₁₀) ∷ (W.run (M.run (P.deregisterProtocol Old.j₁₀))) ∷ (W.run (M.run (P.asyncProtocolResult Old.j₁₀))) ∷ (W.joinGroup owner) ∷ (W.finishGroup owner) ∷ [])
normalPrefix12 : W.Executes normal0 normalPrefix12Actions normal12
normalPrefix12 = W.next normal-edge1 (W.next normal-edge2 (W.next normal-edge3 (W.next normal-edge4 (W.next normal-edge5 (W.next normal-edge6 (W.next normal-edge7 (W.next normal-edge8 (W.next normal-edge9 (W.next normal-edge10 (W.next normal-edge11 (W.next normal-edge12 (W.done))))))))))))
cleanSeedActions : List W.Action
cleanSeedActions = W.run (M.run (P.protocolReturned Old.j₁₀)) ∷ W.run (M.run (P.commitClean Old.j₁₀)) ∷ []
cleanSeedPath : W.Executes (wrap F.error7) cleanSeedActions cleanSeed
cleanSeedPath = W.next clean-seed-returned (W.next clean-seed-committed W.done)
errorSeedActions : List W.Action
errorSeedActions = W.run (M.run (P.protocolException Old.j₁₀ Old.err)) ∷ []
errorSeedPath : W.Executes (wrap F.error7) errorSeedActions errorSeed
errorSeedPath = W.next error-seed-committed W.done
abstract
  initialized-normal-close : W.Executes (wrap (F.wrap Old.b0))
    (map W.run (map M.run Old.startActions ++ F.errorPrefixActions) ++ normalActions) normal30
  initialized-normal-close = append initialized-running normalPath
  initialized-clean-pending-cancellation : W.Executes (wrap (F.wrap Old.b0))
    ((map W.run (map M.run Old.startActions ++ F.errorPrefixActions) ++ cleanSeedActions) ++ cleanCancelActions) cleanCancel15
  initialized-clean-pending-cancellation = append (append initialized-running cleanSeedPath) cleanCancelPath
  initialized-error-normal-outrun : W.Executes (wrap (F.wrap Old.b0))
    ((map W.run (map M.run Old.startActions ++ F.errorPrefixActions) ++ errorSeedActions) ++ errorOutrunsActions) errorOutruns15
  initialized-error-normal-outrun = append (append initialized-running errorSeedPath) errorOutrunsPath
  initialized-replacement : W.Executes (wrap (F.wrap Old.b0))
    ((map W.run (map M.run Old.startActions ++ F.errorPrefixActions) ++ normalPrefix7Actions) ++ replacementActions) replacement10
  initialized-replacement = append (append initialized-running normalPrefix7) replacementPath
  initialized-engineDuringGroup : W.Executes (wrap (F.wrap Old.b0))
    ((map W.run (map M.run Old.startActions ++ F.errorPrefixActions) ++ normalPrefix7Actions) ++ engineDuringGroupActions) engineDuringGroup2
  initialized-engineDuringGroup = append (append initialized-running normalPrefix7) engineDuringGroupPath
  initialized-abortGroup : W.Executes (wrap (F.wrap Old.b0))
    ((map W.run (map M.run Old.startActions ++ F.errorPrefixActions) ++ normalPrefix7Actions) ++ abortGroupActions) abortGroup25
  initialized-abortGroup = append (append initialized-running normalPrefix7) abortGroupPath
  initialized-removedAbort : W.Executes (wrap (F.wrap Old.b0))
    ((map W.run (map M.run Old.startActions ++ F.errorPrefixActions) ++ normalPrefix9Actions) ++ removedAbortActions) removedAbort20
  initialized-removedAbort = append (append initialized-running normalPrefix9) removedAbortPath
  initialized-abortDrain : W.Executes (wrap (F.wrap Old.b0))
    ((map W.run (map M.run Old.startActions ++ F.errorPrefixActions) ++ normalPrefix12Actions) ++ abortDrainActions) abortDrain1
  initialized-abortDrain = append (append initialized-running normalPrefix12) abortDrainPath
  initialized-priority-control : W.Executes (wrap (F.wrap Old.b0))
    (map W.run (map M.run Old.startActions ++ F.errorPrefixActions) ++ priorityActions) priority3
  initialized-priority-control = append initialized-running priorityPath
  initialized-prestartup-stop : W.Executes (wrap (F.wrap Old.b0))
    (map W.run (map M.run (Old.birthPathActions ++ Old.publicationPathActions)) ++ (W.requestShutdown owner ∷ [])) earlyRequested
  initialized-prestartup-stop = append
    (lift-path (F.lift-path (Old.append Old.birthPath Old.publicationPath)) refl)
    (W.next stop-request-before-physical-startup W.done)

-- A separately composed source/physical prefix exposes the masked insertion gap.
forkGapPactions : List P.Action
forkGapPactions = P.control owner P.selectCommand ∷ P.control owner (P.demand 1) ∷
  P.control owner P.sampleTracer ∷ P.control owner P.commitTracer ∷ P.control owner P.finishStart ∷
  P.forkResponder owner Old.j₁₀ Old.r₀ ∷ []
forkGapPpath : P.Executes Old.z12 forkGapPactions Old.r6
forkGapPpath = P.next Old.responder1 (P.next Old.responder2 (P.next Old.responder3
  (P.next Old.responder4 (P.next Old.responder5 (P.next Old.responder6 P.done)))))
abstract
  initialized-fork-gap-control : W.Executes (wrap (F.wrap Old.b0))
    ((map W.run (map M.run Old.startActions) ++ map W.run (map M.run forkGapPactions)) ++ forkGapActions) forkGap1
  initialized-fork-gap-control = append
    (append (lift-path F.initialized-running refl) (lift-path (F.lift-path forkGapPpath) refl)) forkGapPath

abort-status-is-Stopping-until-whole-close : W.source abortGroup20 ≡ W.source abortGroup1
abort-status-is-Stopping-until-whole-close = refl
normal-local-close-keeps-parent-thread-registry :
  B.threads (U.base (P.base (W.protocolState normal30))) ≡ B.threads (U.base (P.base (M.base F.error7)))
normal-local-close-keeps-parent-thread-registry = refl

-- Reuse the generic source/pool proofs and the exact snapshot certificate on
-- these actual initialized executions. Removed history is outside that result.
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ)
import ConnectionManagement.Properties.MuxGroupShutdown as Proofs
module Facts = Proofs F.bearerClosed
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolFacts
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Properties.JobPoolCloseKernel as CloseFacts
module Close = CloseFacts T.TypedResult true
normal-source-and-pools : Facts.Paths (wrap (F.wrap Old.b0)) normal30
normal-source-and-pools = Facts.exec-projects initialized-normal-close
abort-source-and-pools : Facts.Paths (wrap (F.wrap Old.b0)) abortGroup25
abort-source-and-pools = Facts.exec-projects initialized-abortGroup
normal-actual-initial-pool : ProtocolFacts.PTrace Pool.initial (W.poolAt owner normal30)
normal-actual-initial-pool = Facts.pool-from-initial actual-initializer initialized-normal-close owner
normal-captures : Capture.Captures (W.source normal30)
normal-captures = Facts.from-initial-captures actual-initializer initialized-normal-close
normal-supply : Supply.Valid (W.source normal30)
normal-supply = Facts.from-initial-supply actual-initializer Old.Prior.initial-bounds initialized-normal-close
abort-captures : Capture.Captures (W.source abortGroup25)
abort-captures = Facts.from-initial-captures actual-initializer initialized-abortGroup
abort-supply : Supply.Valid (W.source abortGroup25)
abort-supply = Facts.from-initial-supply actual-initializer Old.Prior.initial-bounds initialized-abortGroup
normal-whole-snapshot-terminal : ∀ j → j ∈ Pool.snapshot (W.poolAt owner normal30) → Close.Terminal (W.poolAt owner normal30) j
normal-whole-snapshot-terminal = Facts.whole-closed-from-initial actual-initializer initialized-normal-close owner refl
abort-whole-snapshot-terminal : ∀ j → j ∈ Pool.snapshot (W.poolAt owner abortGroup25) → Close.Terminal (W.poolAt owner abortGroup25) j
abort-whole-snapshot-terminal = Facts.whole-closed-from-initial actual-initializer initialized-abortGroup owner refl
removed-history-whole-snapshot-terminal : ∀ j → j ∈ Pool.snapshot (W.poolAt owner removedAbort20) → Close.Terminal (W.poolAt owner removedAbort20) j
removed-history-whole-snapshot-terminal = Facts.whole-closed-from-initial actual-initializer initialized-removedAbort owner refl

actual-current-mini-capture : Facts.GroupCapture owner (Old.j₁₀ ∷ []) normal4 normal5
actual-current-mini-capture = Facts.capture-observation owner (Old.j₁₀ ∷ []) normal4 normal-edge5
actual-mini-cancel-delivery : Facts.GroupDelivery owner normal6 normal7
actual-mini-cancel-delivery = Facts.delivery-observation owner normal6 normal-edge7
actual-committed-clean-unwind : Facts.ChildUnwind Old.j₁₀ cleanCancel7 cleanCancel8
actual-committed-clean-unwind = Facts.unwind-observation Old.j₁₀ cleanCancel7 cleanCancel-edge8
actual-mini-join-observes-result : Σ JobId (λ j → Facts.GroupJoin owner j normal10 normal11)
actual-mini-join-observes-result = Facts.join-observation owner normal10 normal-edge11
actual-owner-abort : Facts.OwnerAbort owner Old.err normal7 abortGroup1
actual-owner-abort = Facts.abort-observation owner Old.err normal7 abortGroup-edge1
actual-whole-capture : Facts.WholeCapture owner (Old.j₁ ∷ Old.j₀ ∷ []) normal15 normal16
actual-whole-capture = Facts.whole-capture-observation owner (Old.j₁ ∷ Old.j₀ ∷ []) normal15 normal-edge16
actual-whole-finish : Facts.WholeFinish owner normal28 normal29
actual-whole-finish = Facts.whole-finish-observation owner normal28 normal-edge29
committed-clean-slot-is-inactive : P.active owner Mux.responderJob 1 (P.jobs (W.protocolState cleanSeed)) ≡ false
committed-clean-slot-is-inactive = refl
actual-capture-still-includes-registered-clean-job : Facts.GroupCapture owner (Old.j₁₀ ∷ []) cleanCancel4 cleanCancel5
actual-capture-still-includes-registered-clean-job = Facts.capture-observation owner (Old.j₁₀ ∷ []) cleanCancel4 cleanCancel-edge5
actual-removed-history-not-recaptured : Facts.WholeCapture owner (Old.j₁ ∷ Old.j₀ ∷ []) removedAbort1 removedAbort2
actual-removed-history-not-recaptured = Facts.whole-capture-observation owner (Old.j₁ ∷ Old.j₀ ∷ []) removedAbort1 removedAbort-edge2
