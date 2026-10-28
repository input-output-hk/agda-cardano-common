{-# OPTIONS --guardedness #-}

-- Initialized async delivery after a start tracer committed its counters and
-- full event burst, before protocol fork. Named async observations are inputs;
-- no timer/provider progress or source implementation refinement is inferred.
module ConnectionManagement.Negative.MuxCallbackCommitted where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
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
import ConnectionManagement.Negative.MuxCallbackCancellation as Held
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxStartupUnwind as Prior
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
prefixActions : List R.Action
prefixActions = wrapP (P.control owner P.selectCommand) ∷ wrapP (P.control owner (P.demand 1)) ∷
  wrapP (P.control owner P.sampleTracer) ∷ wrapP (P.control owner P.commitTracer) ∷ []
prefixPath : R.Executes (F.wrapP Old.z12) prefixActions (F.wrapP Old.r4)
prefixPath = R.next Held.prefix1 (R.next Held.prefix2 (R.next Held.prefix3 (R.next Held.prefix4 R.done)))
abstract
  initialized-committed : R.Executes Prior.start
    (Prior.wrappedActions Old.startActions ++ prefixActions) (F.wrapP Old.r4)
  initialized-committed = Facts.append Held.initialized-monitor prefixPath
committed : Mux.Mux → List Shared.IGEvent → Pool.State → R.PC → R.State
committed m q pool pc = F.selected (Old.snapshot (Old.sourceMux m q) pool [] [])
  (S.monitoring Old.j₀ Old.j₁) (Mux.afterStart 1) R.poolBody (R.async err) pc
h0 : R.State
h0 = F.wrapP Old.r4
h1 : R.State
h1 = committed Old.m4 Old.messages Prior.k0 R.awaitingClose
h-edge1 : R.step (R.observeCancellation owner R.unmaskedMuxCallback err) h0 ≡ just h1
h-edge1 = refl
h2 : R.State
h2 = committed Old.m4 Old.messages Prior.k1 R.closing
h-edge2 : R.step (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) h1 ≡ just h2
h-edge2 = refl
h3 : R.State
h3 = committed Old.m4 Old.messages Prior.k2 R.closing
h-edge3 : R.step (R.requestCancel owner) h2 ≡ just h3
h-edge3 = refl
h4 : R.State
h4 = committed Old.m4 Old.messages Prior.k3 R.closing
h-edge4 : R.step (R.deliverCancel owner) h3 ≡ just h4
h-edge4 = refl
h5 : R.State
h5 = committed Old.m4 Old.messages Prior.k4 R.closing
h-edge5 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) h4 ≡ just h5
h-edge5 = refl
h6 : R.State
h6 = committed Old.m4 Old.messages Prior.k5 R.closing
h-edge6 : R.step (wrapP (P.deregisterInfra owner T.demuxer)) h5 ≡ just h6
h-edge6 = refl
h7 : R.State
h7 = committed Old.m4 Old.messages Prior.k6 R.closing
h-edge7 : R.step (wrapP (P.asyncInfraResult owner T.demuxer)) h6 ≡ just h7
h-edge7 = refl
h8 : R.State
h8 = committed Old.m4 Old.messages Prior.k7 R.closing
h-edge8 : R.step (R.join owner) h7 ≡ just h8
h-edge8 = refl
h9 : R.State
h9 = committed Old.m4 Old.messages Prior.k8 R.closing
h-edge9 : R.step (R.requestCancel owner) h8 ≡ just h9
h-edge9 = refl
h10 : R.State
h10 = committed Old.m4 Old.messages Prior.k9 R.closing
h-edge10 : R.step (R.deliverCancel owner) h9 ≡ just h10
h-edge10 = refl
h11 : R.State
h11 = committed Old.m4 Old.messages Prior.k10 R.closing
h-edge11 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) h10 ≡ just h11
h-edge11 = refl
h12 : R.State
h12 = committed Old.m4 Old.messages Prior.k11 R.closing
h-edge12 : R.step (wrapP (P.deregisterInfra owner T.muxer)) h11 ≡ just h12
h-edge12 = refl
h13 : R.State
h13 = committed Old.m4 Old.messages Prior.k12 R.closing
h-edge13 : R.step (wrapP (P.asyncInfraResult owner T.muxer)) h12 ≡ just h13
h-edge13 = refl
h14 : R.State
h14 = committed Old.m4 Old.messages Prior.k13 R.closing
h-edge14 : R.step (R.join owner) h13 ≡ just h14
h-edge14 = refl
h15 : R.State
h15 = committed Old.m4 Old.messages Prior.k14 R.poolClosed
h-edge15 : R.step (R.finishClose owner) h14 ≡ just h15
h-edge15 = refl
h16 : R.State
h16 = committed (record Old.m4 { status = Mux.failed err }) Old.messages Prior.k14 R.asyncStatus
h-edge16 : R.step (R.writeAsyncFailure owner) h15 ≡ just h16
h-edge16 = refl
h17 : R.State
h17 = committed (record Old.m4 { status = Mux.failed err; callback = Mux.readActive Mux.muxStopped }) Old.messages Prior.k14 R.asyncDead
h-edge17 : R.step (R.beginDead owner) h16 ≡ just h17
h-edge17 = refl
h18 : R.State
h18 = committed (record Old.m4 { status = Mux.failed err; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages Prior.k14 R.asyncDead
h-edge18 : R.step (R.sampleDead owner) h17 ≡ just h18
h-edge18 = refl
h19 : R.State
h19 = committed (record Old.m4 { status = Mux.failed err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) Prior.k14 R.asyncDead
h-edge19 : R.step (R.commitDead owner) h18 ≡ just h19
h-edge19 = refl
h20 : R.State
h20 = committed (record Old.m4 { status = Mux.failed err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) Prior.k14 R.readyBuffer
h-edge20 : R.step (R.finishDead owner) h19 ≡ just h20
h-edge20 = refl
h21 : R.State
h21 = F.withExit (W.bufferScope (G.asyncExit err)) (committed (record Old.m4 { status = Mux.failed err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) Prior.k14 R.handedOff)
h-edge21 : R.step (R.handoff owner) h20 ≡ just h21
h-edge21 = refl
hActions : List R.Action
hActions = (R.observeCancellation owner R.unmaskedMuxCallback err) ∷ (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) ∷ (wrapP (P.deregisterInfra owner T.demuxer)) ∷ (wrapP (P.asyncInfraResult owner T.demuxer)) ∷ (R.join owner) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) ∷ (wrapP (P.deregisterInfra owner T.muxer)) ∷ (wrapP (P.asyncInfraResult owner T.muxer)) ∷ (R.join owner) ∷ (R.finishClose owner) ∷ (R.writeAsyncFailure owner) ∷ (R.beginDead owner) ∷ (R.sampleDead owner) ∷ (R.commitDead owner) ∷ (R.finishDead owner) ∷ (R.handoff owner) ∷ []
hPath : R.Executes h0 hActions h21
hPath = R.next h-edge1 (R.next h-edge2 (R.next h-edge3 (R.next h-edge4 (R.next h-edge5 (R.next h-edge6 (R.next h-edge7 (R.next h-edge8 (R.next h-edge9 (R.next h-edge10 (R.next h-edge11 (R.next h-edge12 (R.next h-edge13 (R.next h-edge14 (R.next h-edge15 (R.next h-edge16 (R.next h-edge17 (R.next h-edge18 (R.next h-edge19 (R.next h-edge20 (R.next h-edge21 (R.done)))))))))))))))))))))
abstract
  initialized-committed-close : R.Executes Prior.start
    ((Prior.wrappedActions Old.startActions ++ prefixActions) ++ hActions) h21
  initialized-committed-close = Facts.append initialized-committed hPath
committed-burst-survives-failure : Shared.inboundInfo (Machine.world (O.core (R.source h16))) ≡ Old.messages
committed-burst-survives-failure = refl
committed-counters-survive-failure : P.muxAt Old.mid (R.protocols h16) ≡ just (record Old.m4 { status = Mux.failed err })
committed-counters-survive-failure = refl
no-protocol-fork-invented : P.jobs (R.protocols h21) ≡ []
no-protocol-fork-invented = refl
no-abandoned-fork : R.step (wrapP (P.control owner P.finishStart)) h1 ≡ nothing
no-abandoned-fork = refl
no-masked-gap-observation : R.step (R.observeCancellation owner R.unmaskedMuxCallback err) (F.wrapP Old.r6) ≡ nothing
no-masked-gap-observation = refl
source-and-pool-paths : Facts.Paths Prior.start h21
source-and-pool-paths = Facts.exec-projects initialized-committed-close

-- Explicit queue-full input: the new Dead callback may retry. No successful
-- callback return or handler exit is inferred from a completed pool close.
open import Data.List using (replicate)
fullQueue : List Shared.IGEvent
fullQueue = replicate 100 (Shared.muxFinished key₀)
blockedDead : R.State
blockedDead = committed (record Old.m4 { status = Mux.failed err; callback = Mux.commitTrace true Mux.muxStopped })
  fullQueue Prior.k14 R.asyncDead
no-dead-commit-when-full : R.step (R.commitDead owner) blockedDead ≡ nothing
no-dead-commit-when-full = refl
no-dead-finish-when-full : R.step (R.finishDead owner) blockedDead ≡ nothing
no-dead-finish-when-full = refl
no-handoff-when-dead-blocked : R.step (R.handoff owner) blockedDead ≡ nothing
no-handoff-when-dead-blocked = refl
