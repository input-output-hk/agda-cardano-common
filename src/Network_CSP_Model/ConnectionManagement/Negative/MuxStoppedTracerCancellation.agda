{-# OPTIONS --guardedness #-}

-- Initialized cancellation inside the corrected graceful TraceStopped callback.
-- The uncommitted old notification must not be fabricated. Async observations are inputs;
-- no timer/provider progress or source implementation refinement is inferred.
module ConnectionManagement.Negative.MuxStoppedTracerCancellation where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import ConnectionManagement.Store using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.IGTypes using (clean)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.Properties.MuxStartupUnwind as Proof
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Negative.MuxGroupShutdown as GF
import ConnectionManagement.Properties.MuxHandlerExit as ExitProof
import ConnectionManagement.Properties.MuxExitCancellation as CancelProof
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxPoolCloseFixtures as PoolFixtures
import ConnectionManagement.Negative.MuxStartupUnwindFixtures as Fixture
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
private
  module R = Unwind RF.bearerClosed
  module Facts = Proof RF.bearerClosed
  module X = Cancellation RF.bearerClosed
  module W = Exit RF.bearerClosed
  module G = W.G
  module M = G.M
  module P = G.P
  module S = G.Startup
  module Pool = G.Pool
  module F = Fixture RF.bearerClosed Old.owner Old.Prior.captured Old.mid
owner : WorkerId
owner = Old.owner
err : ErrorId
err = errorId 89
wrapAction : M.Action → R.Action
wrapAction a = R.run (X.run (W.run (G.run a)))
wrapP : P.Action → R.Action
wrapP a = wrapAction (M.run a)
module Prior = PoolFixtures Old.j₀ Old.j₁
start : R.State
start = Facts.wrap (W.handlerExitState (G.shutdownState (RF.wrap Old.b0) []) [])
module ExitFacts = ExitProof RF.bearerClosed
module CancelFacts = CancelProof RF.bearerClosed
actionsOf : ∀ {s actions t} → G.Executes s actions t → List G.Action
actionsOf {actions = actions} path = actions
prefixActions : List G.Action
prefixActions = GF.normalPrefix12Actions ++
  (G.drainEmpty owner ∷ G.writeStopped owner ∷ G.observeTraceStopped owner ∷ [])
prefixPath : G.Executes GF.normal0 prefixActions GF.normal14a
prefixPath = GF.append GF.normalPrefix12
  (G.next GF.normal-edge13 (G.next GF.normal-edge14 (G.next GF.normal-edge15 G.done)))
allPrefixActions : List G.Action
allPrefixActions = actionsOf GF.initialized-running ++ prefixActions
abstract
  initialized-callback : R.Executes start
    (map R.run (map X.run (map W.run allPrefixActions))) (Facts.wrap (W.handlerExitState GF.normal14a []))
  initialized-callback = Facts.lift (CancelFacts.lift (ExitFacts.lift-path
    (GF.append GF.initialized-running prefixPath) refl))

originalMux : Mux.Mux
originalMux = record Old.m6 { commands = []; status = Mux.stopped; callback = Mux.readActive Mux.muxStopped }
extraPool : Pool.State → Pool.State
extraPool pool = record pool { handles = Pool.handles pool ++ ((Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ []) }
selected : Mux.Mux → List Shared.IGEvent → Pool.State → R.PC → R.State
selected m queue pool pc = R.unwinding
  (W.handlerExitState (G.shutdownState
    (M.monitorState (Old.snapshot (Old.sourceMux m queue) (extraPool pool)
      ((Old.j₁₀ , Old.rJob T.executing) ∷ []) []) [])
    ((owner , G.frame G.stoppedTracing (Old.j₁₀ ∷ []) [] (Old.j₁₀ ∷ []) G.ready) ∷ [])) [])
  ((owner , R.fault Old.Prior.captured Old.mid (S.monitoring Old.j₀ Old.j₁)
    (Mux.callback originalMux) R.poolBody (R.async err) pc) ∷ [])
h0 : R.State
h0 = Facts.wrap (W.handlerExitState GF.normal14a [])
h1 : R.State
h1 = selected originalMux Old.messages Prior.k0 R.awaitingClose
h-edge1 : R.step (R.observeCancellation owner R.unmaskedMuxCallback err) h0 ≡ just h1
h-edge1 = refl
h2 : R.State
h2 = selected originalMux Old.messages Prior.k1 R.closing
h-edge2 : R.step (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) h1 ≡ just h2
h-edge2 = refl
h3 : R.State
h3 = selected originalMux Old.messages Prior.k2 R.closing
h-edge3 : R.step (R.requestCancel owner) h2 ≡ just h3
h-edge3 = refl
h4 : R.State
h4 = selected originalMux Old.messages Prior.k3 R.closing
h-edge4 : R.step (R.deliverCancel owner) h3 ≡ just h4
h-edge4 = refl
h5 : R.State
h5 = selected originalMux Old.messages Prior.k4 R.closing
h-edge5 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) h4 ≡ just h5
h-edge5 = refl
h6 : R.State
h6 = selected originalMux Old.messages Prior.k5 R.closing
h-edge6 : R.step (wrapP (P.deregisterInfra owner T.demuxer)) h5 ≡ just h6
h-edge6 = refl
h7 : R.State
h7 = selected originalMux Old.messages Prior.k6 R.closing
h-edge7 : R.step (wrapP (P.asyncInfraResult owner T.demuxer)) h6 ≡ just h7
h-edge7 = refl
h8 : R.State
h8 = selected originalMux Old.messages Prior.k7 R.closing
h-edge8 : R.step (R.join owner) h7 ≡ just h8
h-edge8 = refl
h9 : R.State
h9 = selected originalMux Old.messages Prior.k8 R.closing
h-edge9 : R.step (R.requestCancel owner) h8 ≡ just h9
h-edge9 = refl
h10 : R.State
h10 = selected originalMux Old.messages Prior.k9 R.closing
h-edge10 : R.step (R.deliverCancel owner) h9 ≡ just h10
h-edge10 = refl
h11 : R.State
h11 = selected originalMux Old.messages Prior.k10 R.closing
h-edge11 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) h10 ≡ just h11
h-edge11 = refl
h12 : R.State
h12 = selected originalMux Old.messages Prior.k11 R.closing
h-edge12 : R.step (wrapP (P.deregisterInfra owner T.muxer)) h11 ≡ just h12
h-edge12 = refl
h13 : R.State
h13 = selected originalMux Old.messages Prior.k12 R.closing
h-edge13 : R.step (wrapP (P.asyncInfraResult owner T.muxer)) h12 ≡ just h13
h-edge13 = refl
h14 : R.State
h14 = selected originalMux Old.messages Prior.k13 R.closing
h-edge14 : R.step (R.join owner) h13 ≡ just h14
h-edge14 = refl
h15 : R.State
h15 = selected originalMux Old.messages Prior.k14 R.poolClosed
h-edge15 : R.step (R.finishClose owner) h14 ≡ just h15
h-edge15 = refl
h16 : R.State
h16 = selected (record originalMux { status = Mux.failed err }) Old.messages Prior.k14 R.asyncStatus
h-edge16 : R.step (R.writeAsyncFailure owner) h15 ≡ just h16
h-edge16 = refl
h17 : R.State
h17 = selected (record originalMux { status = Mux.failed err; callback = Mux.readActive Mux.muxStopped }) Old.messages Prior.k14 R.asyncDead
h-edge17 : R.step (R.beginDead owner) h16 ≡ just h17
h-edge17 = refl
h18 : R.State
h18 = selected (record originalMux { status = Mux.failed err; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages Prior.k14 R.asyncDead
h-edge18 : R.step (R.sampleDead owner) h17 ≡ just h18
h-edge18 = refl
h19 : R.State
h19 = selected (record originalMux { status = Mux.failed err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) Prior.k14 R.asyncDead
h-edge19 : R.step (R.commitDead owner) h18 ≡ just h19
h-edge19 = refl
h20 : R.State
h20 = selected (record originalMux { status = Mux.failed err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) Prior.k14 R.readyBuffer
h-edge20 : R.step (R.finishDead owner) h19 ≡ just h20
h-edge20 = refl
h21 : R.State
h21 = F.withExit (W.bufferScope (G.asyncExit err)) (selected (record originalMux { status = Mux.failed err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) Prior.k14 R.handedOff)
h-edge21 : R.step (R.handoff owner) h20 ≡ just h21
h-edge21 = refl
hActions : List R.Action
hActions = (R.observeCancellation owner R.unmaskedMuxCallback err) ∷ (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) ∷ (wrapP (P.deregisterInfra owner T.demuxer)) ∷ (wrapP (P.asyncInfraResult owner T.demuxer)) ∷ (R.join owner) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) ∷ (wrapP (P.deregisterInfra owner T.muxer)) ∷ (wrapP (P.asyncInfraResult owner T.muxer)) ∷ (R.join owner) ∷ (R.finishClose owner) ∷ (R.writeAsyncFailure owner) ∷ (R.beginDead owner) ∷ (R.sampleDead owner) ∷ (R.commitDead owner) ∷ (R.finishDead owner) ∷ (R.handoff owner) ∷ []
hPath : R.Executes h0 hActions h21
hPath = R.next h-edge1 (R.next h-edge2 (R.next h-edge3 (R.next h-edge4 (R.next h-edge5 (R.next h-edge6 (R.next h-edge7 (R.next h-edge8 (R.next h-edge9 (R.next h-edge10 (R.next h-edge11 (R.next h-edge12 (R.next h-edge13 (R.next h-edge14 (R.next h-edge15 (R.next h-edge16 (R.next h-edge17 (R.next h-edge18 (R.next h-edge19 (R.next h-edge20 (R.next h-edge21 (R.done)))))))))))))))))))))
abstract
  initialized-interrupted-stopped-close : R.Executes start
    (map R.run (map X.run (map W.run allPrefixActions)) ++ hActions) h21
  initialized-interrupted-stopped-close = Facts.append initialized-callback hPath
no-old-active-read : R.step (R.run (X.run (W.run (G.sampleStoppedTracer owner)))) h1 ≡ nothing
no-old-active-read = refl
no-old-graceful-return : R.step (R.run (X.run (W.run (G.finishStoppedTrace owner)))) h1 ≡ nothing
no-old-graceful-return = refl
no-early-failure : R.step (R.writeAsyncFailure owner) h1 ≡ nothing
no-early-failure = refl
no-old-notification-before-new-dead : Shared.inboundInfo (Machine.world (O.core (R.source h16))) ≡ Old.messages
no-old-notification-before-new-dead = refl
one-new-dead-notification : Shared.inboundInfo (Machine.world (O.core (R.source h21))) ≡
  Old.messages ++ (Shared.muxFinished key₀ ∷ [])
one-new-dead-notification = refl
original-callback-retained : lookup owner (R.faults h21) ≡ just
  (R.fault Old.Prior.captured Old.mid (S.monitoring Old.j₀ Old.j₁)
    (Mux.callback originalMux) R.poolBody (R.async err) R.handedOff)
original-callback-retained = refl
source-and-pool-paths : Facts.Paths start h21
source-and-pool-paths = Facts.exec-projects initialized-interrupted-stopped-close

actual-initializer : R.initial (O.initial Old.F.start) ≡ just start
actual-initializer = refl
