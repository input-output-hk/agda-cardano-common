{-# OPTIONS --guardedness #-}

-- Initialized replacement from the masked post-close catch. A blocking caller
-- tracer is an observed contract; full-queue controls below are conditional.
module ConnectionManagement.Negative.MuxCatchUnwind where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; map; take; replicate)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.MuxCatchUnwind as Catch
import ConnectionManagement.Properties.MuxCatchUnwind as CatchFacts
import ConnectionManagement.Negative.MuxInitiatorTraceEffects as E
import ConnectionManagement.Negative.MuxDeltaQ as Base
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
module C = Catch RF.bearerClosed
module Facts = CatchFacts RF.bearerClosed
module D = E.D
module R = E.R
module X = E.X
module W = E.W
module P = E.P
module Pool = E.Pool
module F = E.F
module Clean = E.Clean
owner : WorkerId
owner = Old.owner
err : ErrorId
err = errorId 91
wrap : D.State → C.State
wrap d = C.catchState d []
initial : C.State
initial = wrap Base.start
actual-initializer : C.initial (O.initial Old.F.start) ≡ just initial
actual-initializer = refl

-- Evidence that lifting the prefix never bypasses the new metadata guard.
allAllowed : List D.Action → Bool
allAllowed [] = true
allAllowed (a ∷ as) = C.allowed a ∧ allAllowed as
tag : ∀ actions → allAllowed actions ≡ true → Facts.AllowedActions actions
tag [] ok = Facts.empty
tag (a ∷ as) ok with C.allowed a in allowed
... | false = case ok of λ ()
... | true = Facts.more allowed (tag as ok)
originalActions : E.Origin → List D.Action
originalActions origin = (E.readyActions origin ++ E.Close.actions origin (R.async E.err)) ++
  take 2 (E.Async.actions origin)
original-tags : ∀ origin → Facts.AllowedActions (originalActions origin)
original-tags E.cleanCompletion = tag (originalActions E.cleanCompletion) refl
original-tags E.errorCompletion = tag (originalActions E.errorCompletion) refl

module Scenario (origin : E.Origin) where
  module A = E.Async origin
  module PC = E.Close origin (R.async E.err)
  original : D.Executes Base.start (originalActions origin) A.a17
  original = E.Prefix.append PC.initialized (D.next A.edge16 (D.next A.edge17 D.done))
  prefix : C.Executes initial (map C.run (originalActions origin)) (wrap A.a17)
  prefix = Facts.lift original (original-tags origin)
  caught : R.Fault
  caught = R.fault Old.Prior.captured Old.mid (E.S.monitoring Old.j₀ Old.j₁)
    Mux.returned R.poolBody (R.async E.err) R.asyncDead
  interrupted : C.Interrupted
  interrupted = C.interrupted caught (Mux.readActive Mux.muxStopped) (C.cancellation C.blockedCallerTracer err)
  changed : R.PC → D.State
  changed stage = record A.a17 { base = record (D.base A.a17)
    { faults = (owner , record caught { outcome = R.async err; phase = stage }) ∷ [] } }
  at : D.State → C.State
  at d = C.catchState d ((owner , interrupted) ∷ [])
  after : W.Phase → D.State
  after stage = record (changed R.handedOff) { base = F.withExit stage (D.base (changed R.handedOff)) }
  cleaned : W.Phase → Shared.State → D.State
  cleaned stage world = record (after stage) { base = F.withWorld world (D.base (after stage)) }
  s0 : C.State
  s0 = wrap A.a17
  s1 : C.State
  s1 = at (changed R.readyBuffer)
  edge1 : C.step (C.observeCancellation owner C.blockedCallerTracer err) s0 ≡ just s1
  edge1 = refl
  s2 : C.State
  s2 = at (after (W.bufferScope (E.G.asyncExit err)))
  s3 : C.State
  s3 = at (after (W.bodyExited (W.asyncException err)))
  s4 : C.State
  s4 = at (cleaned (W.finalizing (W.asyncException err)) (Clean.world1 (F.shared (D.base A.a17))))
  s5 : C.State
  s5 = at (cleaned (W.finalizing (W.asyncException err)) (Clean.world2 (F.shared (D.base A.a17))))
  s6 : C.State
  s6 = at (cleaned (W.finalizing (W.asyncException err)) (Clean.world3 (F.shared (D.base A.a17))))
  s7 : C.State
  s7 = at (cleaned (W.finalizing (W.asyncException err)) (Clean.world4 (F.shared (D.base A.a17))))
  s8 : C.State
  s8 = at (cleaned (W.finalizing (W.asyncException err)) (Clean.world5 (F.shared (D.base A.a17))))
  s9 : C.State
  s9 = at (cleaned (W.finalizing (W.asyncException err)) (Clean.world6 (F.shared (D.base A.a17))))
  s10 : C.State
  s10 = at (cleaned (W.cleanupComplete (W.asyncException err) Shared.cleanupNormal) (Clean.world6 (F.shared (D.base A.a17))))
  s11 : C.State
  s11 = at (cleaned (W.resultAvailable (W.asyncException err) Shared.cleanupNormal) (Clean.world6 (F.shared (D.base A.a17))))
  edge2 : C.step (C.run (D.run (R.handoff owner))) s1 ≡ just s2
  edge2 = refl
  edge3 : C.step (C.run (D.run (R.run (X.run (W.observeBufferReturn owner))))) s2 ≡ just s3
  edge3 = refl
  edge4 : C.step (C.run (D.run (R.run (X.run (W.enterFinalizer owner))))) s3 ≡ just s4
  edge4 = refl
  edge5 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap))))) s4 ≡ just s5
  edge5 = refl
  edge6 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry))))) s5 ≡ just s6
  edge6 = refl
  edge7 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket))))) s6 ≡ just s7
  edge7 = refl
  edge8 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap))))) s7 ≡ just s8
  edge8 = refl
  edge9 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters))))) s8 ≡ just s9
  edge9 = refl
  edge10 : C.step (C.run (D.run (R.run (X.run (W.finishCleanup owner))))) s9 ≡ just s10
  edge10 = refl
  edge11 : C.step (C.run (D.run (R.run (X.run (W.publishAsyncResult owner))))) s10 ≡ just s11
  edge11 = refl
  actions : List C.Action
  actions = (C.observeCancellation owner C.blockedCallerTracer err) ∷ (C.run (D.run (R.handoff owner))) ∷ (C.run (D.run (R.run (X.run (W.observeBufferReturn owner))))) ∷ (C.run (D.run (R.run (X.run (W.enterFinalizer owner))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters))))) ∷ (C.run (D.run (R.run (X.run (W.finishCleanup owner))))) ∷ (C.run (D.run (R.run (X.run (W.publishAsyncResult owner))))) ∷ []
  path : C.Executes s0 actions s11
  path = C.next edge1 (C.next edge2 (C.next edge3 (C.next edge4 (C.next edge5 (C.next edge6 (C.next edge7 (C.next edge8 (C.next edge9 (C.next edge10 (C.next edge11 (C.done)))))))))))
  abstract
    initialized : C.Executes initial (map C.run (originalActions origin) ++ actions) s11
    initialized = Facts.append prefix path
  replacement-result : W.resultOf owner (R.base (D.base (C.base s11))) ≡ just (W.asyncException err)
  replacement-result = refl
  original-status-retained : P.muxAt Old.mid (R.protocols (D.base (C.base s11))) ≡ just
    (record (E.mux origin) { status = Mux.failed E.err; callback = Mux.readActive Mux.muxStopped })
  original-status-retained = refl
  original-queue-retained : Shared.inboundInfo (Machine.world (O.core (C.source s11))) ≡ E.queue origin
  original-queue-retained = refl
  caught-and-abandoned-retained : lookup owner (C.interruptions s11) ≡ just interrupted
  caught-and-abandoned-retained = refl
  pool-remains-closed : Pool.phase (C.poolAt owner s11) ≡ Pool.closedPool
  pool-remains-closed = refl
  no-second-Failed : C.step (C.run (D.run (R.writeAsyncFailure owner))) s1 ≡ nothing
  no-second-Failed = refl
  no-second-Dead : C.step (C.run (D.run (R.beginDead owner))) s1 ≡ nothing
  no-second-Dead = refl
  no-returned-Dead : C.step (C.run (D.run (R.finishDead owner))) s1 ≡ nothing
  no-returned-Dead = refl
  no-delivery-at-ordinary-STM : C.step (C.observeCancellation owner C.blockedCallerTracer err) (wrap A.a16) ≡ nothing
  no-delivery-at-ordinary-STM = refl
  no-delivery-after-Dead-return : C.step (C.observeCancellation owner C.blockedCallerTracer err) (wrap A.a19) ≡ nothing
  no-delivery-after-Dead-return = refl
  no-queue-delivery-with-room : C.step (C.observeCancellation owner C.retryingIGDead err) (wrap A.a18) ≡ nothing
  no-queue-delivery-with-room = refl
  captures : Capture.Captures (C.source s11)
  captures = Facts.from-initial-captures actual-initializer initialized
  supply : Supply.Valid (C.source s11)
  supply = Facts.from-initial-supply actual-initializer Old.Prior.initial-bounds initialized

module CleanOrigin = Scenario E.cleanCompletion
module ErrorOrigin = Scenario E.errorCompletion

-- Conditional full-queue control: the queue is injected, not proved reachable
-- by the initialized prefixes above. Retry is checked before async receipt.
module FullQueue where
  module S = Scenario E.cleanCompletion
  full : List Shared.IGEvent
  full = replicate 100 (Shared.muxFinished key₀)
  beforeD : D.State
  beforeD = E.asyncAt E.cleanCompletion R.asyncDead (Mux.commitTrace true Mux.muxStopped)
    (E.counters E.cleanCompletion) full
  before : C.State
  before = wrap beforeD
  after : C.State
  after = C.catchState (record beforeD { base = record (D.base beforeD)
    { faults = (owner , record S.caught { outcome = R.async err; phase = R.readyBuffer }) ∷ [] } })
    ((owner , C.interrupted S.caught (Mux.commitTrace true Mux.muxStopped) (C.cancellation C.retryingIGDead err)) ∷ [])
  transaction-retries : C.step (C.run (D.run (R.commitDead owner))) before ≡ nothing
  transaction-retries = refl
  retry-admits-masked-delivery : C.step (C.observeCancellation owner C.retryingIGDead err) before ≡ just after
  retry-admits-masked-delivery = refl
  retry-retains-source-and-queue : C.source after ≡ C.source before
  retry-retains-source-and-queue = refl

-- Synchronous caller-tracer throwing also replaces the caught exception; it
-- cannot bypass the retained observation through the old adapter entry point.
module Synchronous where
  module S = Scenario E.errorCompletion
  module A = E.Async E.errorCompletion
  after : C.State
  after = C.catchState (record A.a17 { base = record (D.base A.a17)
    { faults = (owner , record S.caught { outcome = R.sync err; phase = R.readyBuffer }) ∷ [] } })
    ((owner , C.interrupted S.caught (Mux.readActive Mux.muxStopped) (C.synchronous err)) ∷ [])
  exception-selects-replacement : C.step (C.observeException owner err) S.s0 ≡ just after
  exception-selects-replacement = refl
  legacy-cannot-discard-caught-data : C.step (C.run (D.run (R.observeDeadTraceException owner err))) S.s0 ≡ nothing
  legacy-cannot-discard-caught-data = refl
