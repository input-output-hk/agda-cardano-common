{-# OPTIONS --guardedness #-}

-- TraceStopped source effects, queue-capacity retry and no-IG/inactive controls.
-- Initialized graceful paths live in MuxGroupShutdown; injected full/inactive
-- snapshots below are conditional controls, not source reachability claims.
module ConnectionManagement.Negative.MuxStoppedTracer where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Scenarios.Admission using (key₀)
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Properties.MuxGroupShutdown as GroupProof
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxGroupShutdown as F
import ConnectionManagement.Negative.MuxProtocolJobs as Old
module G = F.W
module P = G.P
module Pool = G.Pool
module Facts = GroupProof RF.bearerClosed
owner : WorkerId
owner = Old.owner

-- Preserve the physical history/registry from the actual pre-trace boundary.
at : Bool → Mux.Mux → List Shared.IGEvent → G.Phase → G.State
at active m queue pc = G.setPhase owner pc (G.setSource config F.normal14)
  where
  original : O.Configuration
  original = Old.sourceMux m queue
  ig : IG.Runtime
  ig = Machine.inboundGovernor (O.core original)
  config : O.Configuration
  config = record original { core = record (O.core original)
    { inboundGovernor = record ig { execution = record (IG.execution ig) { active = active } } } }
stopped : Mux.Mux
stopped = record Old.m6 { commands = []; status = Mux.stopped }

no-return-before-invocation : G.step (G.finishStoppedTrace owner) F.normal14 ≡ nothing
no-return-before-invocation = refl
no-return-before-active-read : G.step (G.finishStoppedTrace owner) F.normal14a ≡ nothing
no-return-before-active-read = refl
no-return-before-transaction : G.step (G.finishStoppedTrace owner) F.normal14b ≡ nothing
no-return-before-transaction = refl
no-whole-close-before-return : G.step (G.beginWholeClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) F.normal14c ≡ nothing
no-whole-close-before-return = refl
no-second-trace-invocation : G.step (G.observeTraceStopped owner) F.normal14a ≡ nothing
no-second-trace-invocation = refl
callback-status-remains-stopped : P.muxAt Old.mid (G.protocolState F.normal14c) ≡ just
  (record stopped { traceCounters = nothing })
callback-status-remains-stopped = refl
callback-does-not-close-pool : Pool.phase (G.poolAt owner F.normal14c) ≡ Pool.openPool
callback-does-not-close-pool = refl

fullQueue : List Shared.IGEvent
fullQueue = replicate 100 (Shared.muxFinished key₀)
blocked : G.State
blocked = at true (record stopped { callback = Mux.commitTrace true Mux.muxStopped }) fullQueue G.stoppedTracing
full-queue-retries : G.step (G.commitStoppedTracer owner) blocked ≡ nothing
full-queue-retries = refl
full-queue-cannot-return : G.step (G.finishStoppedTrace owner) blocked ≡ nothing
full-queue-cannot-return = refl
full-queue-cannot-close : G.step (G.beginWholeClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) blocked ≡ nothing
full-queue-cannot-close = refl

-- A free slot allows one atomic notification/counter-clear transaction.
roomQueue : List Shared.IGEvent
roomQueue = replicate 99 (Shared.muxFinished key₀)
roomBefore roomAfter : G.State
roomBefore = at true (record stopped { callback = Mux.commitTrace true Mux.muxStopped }) roomQueue G.stoppedTracing
roomAfter = at true (record stopped { traceCounters = nothing })
  (roomQueue ++ (Shared.muxFinished key₀ ∷ [])) G.stoppedTracing
one-slot-commits-both-effects : G.step (G.commitStoppedTracer owner) roomBefore ≡ just roomAfter
one-slot-commits-both-effects = refl

-- Active was sampled before the transaction. A later deactivation does not
-- retroactively suppress an already captured True sample.
sampledTrue : G.State
sampledTrue = at false (record stopped { callback = Mux.commitTrace true Mux.muxStopped }) Old.messages G.stoppedTracing
sampledTrueAfter : G.State
sampledTrueAfter = at false (record stopped { traceCounters = nothing })
  (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) G.stoppedTracing
sample-before-deactivate-is-retained : G.step (G.commitStoppedTracer owner) sampledTrue ≡ just sampledTrueAfter
sample-before-deactivate-is-retained = refl

inactive0 inactive1 inactive2 inactive3 inactive4 : G.State
inactive0 = at false stopped fullQueue G.stoppedTrace
inactive1 = at false (record stopped { callback = Mux.readActive Mux.muxStopped }) fullQueue G.stoppedTracing
inactive2 = at false (record stopped { callback = Mux.commitTrace false Mux.muxStopped }) fullQueue G.stoppedTracing
inactive3 = at false stopped fullQueue G.stoppedTracing
inactive4 = at false stopped fullQueue G.monitorReturnedNormal
inactive-invokes : G.step (G.observeTraceStopped owner) inactive0 ≡ just inactive1
inactive-invokes = refl
inactive-samples : G.step (G.sampleStoppedTracer owner) inactive1 ≡ just inactive2
inactive-samples = refl
inactive-skips-transaction : G.step (G.commitStoppedTracer owner) inactive2 ≡ just inactive3
inactive-skips-transaction = refl
inactive-returns : G.step (G.finishStoppedTrace owner) inactive3 ≡ just inactive4
inactive-returns = refl

-- An unattached IG tracer is distinct from an attached but inactive tracer.
noIG : Mux.Mux
noIG = record stopped { tracerAttachment = Mux.noIGTracer }
noIG0 noIG1 noIG2 : G.State
noIG0 = at true noIG fullQueue G.stoppedTrace
noIG1 = at true noIG fullQueue G.stoppedTracing
noIG2 = at true noIG fullQueue G.monitorReturnedNormal
unattached-trace-returns-without-IG-effect : G.step (G.observeTraceStopped owner) noIG0 ≡ just noIG1
unattached-trace-returns-without-IG-effect = refl
unattached-monitor-return : G.step (G.finishStoppedTrace owner) noIG1 ≡ just noIG2
unattached-monitor-return = refl

-- After the callback returned, ordinary unmasked owner cancellation retains
-- its already committed notification; pending callbacks still cannot use it.
afterCommitAbort : G.State
afterCommitAbort = G.setPhase owner (G.ownerAborting Old.err) F.normal14c
returned-callback-can-observe-owner-abort : G.step (G.abortOwner owner Old.err) F.normal14c ≡ just afterCommitAbort
returned-callback-can-observe-owner-abort = refl
pending-callback-cannot-use-returned-abort : G.step (G.abortOwner owner Old.err) F.normal14b ≡ nothing
pending-callback-cannot-use-returned-abort = refl

-- The generic return certificate exposes the actual lookup/status/callback
-- evidence used by initialized graceful downstream exit/cleanup witnesses.
actual-return-certificate : Facts.StoppedReturn owner F.normal14c F.normal15
actual-return-certificate = Facts.finish-stopped-observation owner F.normal14c F.normal-edge15c
