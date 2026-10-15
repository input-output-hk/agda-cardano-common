{-# OPTIONS --guardedness #-}

-- Exhaustive IG dispatcher preservation, without a covered-action premise.
module ConnectionManagement.Properties.HandlerIG where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
import ConnectionManagement.Properties.HandlerIGBoundary as Boundary
import ConnectionManagement.Properties.HandlerIGStartup as Startup
import ConnectionManagement.Properties.HandlerIGMux as Mux
import ConnectionManagement.Properties.HandlerIGLoop as Loop
import ConnectionManagement.Rules.IGRegistration as IG

step-preserves : ∀ a c {c′} → advance (igStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves IG.commitDecision = Boundary.step-preserves IG.commitDecision Boundary.decision
step-preserves (IG.installHandle hid mid k ps flow) = Boundary.step-preserves (IG.installHandle hid mid k ps flow) Boundary.install
step-preserves IG.runResponders = Startup.step-preserves IG.runResponders Startup.start
step-preserves IG.restart = Startup.step-preserves IG.restart Startup.restart
step-preserves IG.requestFailedStop = Startup.step-preserves IG.requestFailedStop Startup.failedStop
step-preserves (IG.sampleTracer mid) = Mux.step-preserves (IG.sampleTracer mid) Mux.sample
step-preserves (IG.commitTracer mid) = Mux.step-preserves (IG.commitTracer mid) Mux.trace
step-preserves (IG.finishStart mid) = Mux.step-preserves (IG.finishStart mid) Mux.started
step-preserves (IG.forkResponder mid) = Mux.step-preserves (IG.forkResponder mid) Mux.fork
step-preserves (IG.monitorCommand mid) = Mux.step-preserves (IG.monitorCommand mid) Mux.command
step-preserves (IG.monitorCompletion mid) = Mux.step-preserves (IG.monitorCompletion mid) Mux.completion
step-preserves (IG.startOnDemand mid n) = Mux.step-preserves (IG.startOnDemand mid n) Mux.demand
step-preserves (IG.finishProtocol mid n outcome) = Mux.step-preserves (IG.finishProtocol mid n outcome) Mux.jobFinished
step-preserves (IG.publishJobResult mid n) = Mux.step-preserves (IG.publishJobResult mid n) Mux.jobResult
step-preserves (IG.finishStop mid) = Mux.step-preserves (IG.finishStop mid) Mux.stopped
step-preserves IG.deactivateIG = Loop.step-preserves IG.deactivateIG Loop.deactivate
step-preserves IG.flushOnExit = Loop.step-preserves IG.flushOnExit Loop.flush
step-preserves (IG.captureTime time) = Loop.step-preserves (IG.captureTime time) Loop.capture
step-preserves IG.registerInactivity = Loop.step-preserves IG.registerInactivity Loop.inactivity
step-preserves IG.selectBatch = Loop.step-preserves IG.selectBatch Loop.select
step-preserves IG.readEvent = Loop.step-preserves IG.readEvent Loop.read
step-preserves IG.registerIdleTimer = Loop.step-preserves IG.registerIdleTimer Loop.idleTimer
step-preserves IG.finishBatch = Loop.step-preserves IG.finishBatch Loop.finish
step-preserves IG.pollStopped = Loop.step-preserves IG.pollStopped Loop.poll
step-preserves (IG.expireTimer tid) = Loop.step-preserves (IG.expireTimer tid) Loop.expire
