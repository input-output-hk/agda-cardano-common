{-# OPTIONS --guardedness #-}

-- Every successful IG action retains existing table references.
module ConnectionManagement.Properties.IGRetention where

open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Properties.IGTableRetention
import ConnectionManagement.Properties.IGBoundaryRetention as Boundary
import ConnectionManagement.Properties.StartupRetention as Startup
import ConnectionManagement.Properties.MuxRetention as Mux
import ConnectionManagement.Properties.LoopRetention as Loop
import ConnectionManagement.Rules.IGRegistration as IG

mode-retains : ∀ mode a ig queue {ig′ queue′} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Retains ig ig′
mode-retains mode IG.commitDecision ig queue eq = Boundary.mode-retains mode IG.commitDecision Boundary.decision ig queue eq
mode-retains mode (IG.installHandle hid mid k ps flow) ig queue eq = Boundary.mode-retains mode (IG.installHandle hid mid k ps flow) Boundary.install ig queue eq
mode-retains mode (IG.installOutboundHandle hid mid k ps flow) ig queue eq = Boundary.mode-retains mode (IG.installOutboundHandle hid mid k ps flow) Boundary.installOutbound ig queue eq
mode-retains mode IG.runResponders ig queue eq = from-anchors (Startup.mode-anchors mode IG.runResponders Startup.start ig queue eq)
mode-retains mode IG.restart ig queue eq = from-anchors (Startup.mode-anchors mode IG.restart Startup.restart ig queue eq)
mode-retains mode IG.requestFailedStop ig queue eq = from-anchors (Startup.mode-anchors mode IG.requestFailedStop Startup.failedStop ig queue eq)
mode-retains mode (IG.sampleTracer mid) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.sampleTracer mid) Mux.sample ig queue eq)
mode-retains mode (IG.commitTracer mid) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.commitTracer mid) Mux.trace ig queue eq)
mode-retains mode (IG.finishStart mid) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.finishStart mid) Mux.started ig queue eq)
mode-retains mode (IG.forkResponder mid) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.forkResponder mid) Mux.fork ig queue eq)
mode-retains mode (IG.monitorCommand mid) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.monitorCommand mid) Mux.command ig queue eq)
mode-retains mode (IG.monitorCompletion mid) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.monitorCompletion mid) Mux.completion ig queue eq)
mode-retains mode (IG.startOnDemand mid n) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.startOnDemand mid n) Mux.demand ig queue eq)
mode-retains mode (IG.finishProtocol mid n outcome) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.finishProtocol mid n outcome) Mux.jobFinished ig queue eq)
mode-retains mode (IG.publishJobResult mid n) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.publishJobResult mid n) Mux.jobResult ig queue eq)
mode-retains mode (IG.finishStop mid) ig queue eq = from-anchors (Mux.mode-anchors mode (IG.finishStop mid) Mux.stopped ig queue eq)
mode-retains mode IG.deactivateIG ig queue eq = from-anchors (Loop.mode-anchors mode IG.deactivateIG Loop.deactivate ig queue eq)
mode-retains mode IG.flushOnExit ig queue eq = from-anchors (Loop.mode-anchors mode IG.flushOnExit Loop.flush ig queue eq)
mode-retains mode (IG.captureTime time) ig queue eq = from-anchors (Loop.mode-anchors mode (IG.captureTime time) Loop.capture ig queue eq)
mode-retains mode IG.registerInactivity ig queue eq = from-anchors (Loop.mode-anchors mode IG.registerInactivity Loop.inactivity ig queue eq)
mode-retains mode IG.selectBatch ig queue eq = from-anchors (Loop.mode-anchors mode IG.selectBatch Loop.select ig queue eq)
mode-retains mode IG.readEvent ig queue eq = from-anchors (Loop.mode-anchors mode IG.readEvent Loop.read ig queue eq)
mode-retains mode IG.registerIdleTimer ig queue eq = from-anchors (Loop.mode-anchors mode IG.registerIdleTimer Loop.idleTimer ig queue eq)
mode-retains mode IG.finishBatch ig queue eq = from-anchors (Loop.mode-anchors mode IG.finishBatch Loop.finish ig queue eq)
mode-retains mode IG.pollStopped ig queue eq = from-anchors (Loop.mode-anchors mode IG.pollStopped Loop.poll ig queue eq)
mode-retains mode (IG.expireTimer tid) ig queue eq = from-anchors (Loop.mode-anchors mode (IG.expireTimer tid) Loop.expire ig queue eq)
