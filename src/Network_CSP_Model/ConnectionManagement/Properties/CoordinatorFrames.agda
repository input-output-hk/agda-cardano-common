{-# OPTIONS --guardedness #-}

-- SI5b, lower half: every wrapper step from the mux handler layer up to the
-- publication-unwind layer leaves the CM shutdown coordinator unchanged or
-- advances it by real coordinator steps. A wait that closes the coordinator
-- is an actual wrapper transition whose oracle is that wrapper's physical
-- handler-result table (the handler or the exit wrapper). No progress or
-- eventual close is asserted.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.CoordinatorFrames (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.IGTypes using (clean; errored)
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.OutboundRelease as Release
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxExitCancellation as CancellationModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxDeltaQ as DeltaQModel
import ConnectionManagement.MuxCatchUnwind as CatchModel
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.Properties.CMShutdown as CloseProof
import ConnectionManagement.Properties.HandlerSupervision as Handler
import ConnectionManagement.Properties.MuxHandlerSupervision as MuxFacts
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Properties.HandlerAuxBacking as Aux
module U = MuxModel Types.TypedResult
module P = ProtocolModel
module M = MonitorModel isBearerClosed
module G = GroupModel isBearerClosed
module W = ExitModel isBearerClosed
module X = CancellationModel isBearerClosed
module R = UnwindModel isBearerClosed
module D = DeltaQModel isBearerClosed
module C = CatchModel isBearerClosed
module N = PublicationModel isBearerClosed
private
  module UF = MuxFacts Types.TypedResult
  module EF = ExitFacts isBearerClosed

CTrace : Close.State → Close.State → Set
CTrace = Handler.CTrace

-- The exit wrapper's own final wait, with the result table it read.
record ExitWait (c : Close.State) : Set where
  constructor exitWait
  field before after : W.State
        actual-control : W.control Close.finishClose before ≡ just after
        same-coordinator : W.shutdown after ≡ c
        primitive-wait : CloseProof.FinalWait c
        physical-oracle : CloseProof.available primitive-wait ≡ (λ w → W.resultReady w before)
open ExitWait public

-- A closed coordinator was closed by an actual physical wait.
Last : Close.State → Set
Last c = Close.phase c ≡ Close.closed → Handler.PhysicalWait c ⊎ ExitWait c

-- Real coordinator steps between two observations, and the closing witness.
record Frame (p q : Close.State) : Set where
  constructor frame
  field trace : CTrace p q
        last : Last p → Last q
open Frame public

stay : ∀ p → Frame p p
stay p = frame ([] , Close.done) (λ l → l)
same : ∀ {p q} → q ≡ p → Frame p q
same {p} refl = stay p
compose : ∀ {p q r} → Frame p q → Frame q r → Frame p r
compose (frame (as , ap) l₁) (frame (bs , bp) l₂) = frame (as ++ bs , Handler.append-close ap bp) (λ l → l₂ (l₁ l))

-- Closed admits no coordinator step.
closed-step : ∀ current available a p {q} → Close.phase p ≡ Close.closed → Close.step current available a p ≡ just q → ⊥
closed-step current available Close.captureSnapshot (Close.shutdownState .Close.closed snap rest ws) refl eq = case eq of λ ()
closed-step current available Close.readEntry (Close.shutdownState .Close.closed snap rest ws) refl eq = case eq of λ ()
closed-step current available Close.requestCancellation (Close.shutdownState .Close.closed snap rest ws) refl eq = case eq of λ ()
closed-step current available Close.acknowledgeDelivery (Close.shutdownState .Close.closed snap rest ws) refl eq = case eq of λ ()
closed-step current available Close.finishTraversal (Close.shutdownState .Close.closed snap rest ws) refl eq = case eq of λ ()
closed-step current available Close.finishClose (Close.shutdownState .Close.closed snap rest ws) refl eq = case eq of λ ()
closed-stuck : ∀ {p as q} → Close.phase p ≡ Close.closed → Close.Executes p as q → q ≡ p
closed-stuck closed Close.done = refl
closed-stuck {p} closed (Close.next {a = a} {current = current} {available = available} eq rest) =
  ⊥-elim (closed-step current available a p closed eq)
closed-frame : ∀ {p q} → Frame p q → Close.phase p ≡ Close.closed → q ≡ p
closed-frame (frame (as , path) last) closed = closed-stuck closed path

phase-cases : ∀ pc → pc ≡ Close.closed ⊎ pc ≢ Close.closed
phase-cases Close.initial = inj₂ (λ ())
phase-cases Close.reading = inj₂ (λ ())
phase-cases Close.awaitResults = inj₂ (λ ())
phase-cases Close.closed = inj₁ refl
phase-cases (Close.sendReady e w) = inj₂ (λ ())
phase-cases (Close.awaitDelivery e w) = inj₂ (λ ())

-- One non-final coordinator step cannot produce the closed phase.
step-frame : ∀ current available a p {q} → Close.step current available a p ≡ just q → a ≢ Close.finishClose → Frame p q
step-frame current available a p eq notFinal = frame ((a ∷ []) , Close.next {current = current} {available = available} eq Close.done)
  (λ _ closed → ⊥-elim (Handler.not-final-close current available a p eq notFinal closed))

-- Lower wrapper paths retain the handler-level physical final wait.
from-handler : ∀ {p q} → CTrace p q → (Handler.LastValid p → Handler.LastValid q) → Frame p q
from-handler {p} {q} (as , path) lower = frame (as , path) lift
  where
  lift : Last p → Last q
  lift lp closedq with phase-cases (Close.phase p)
  ... | inj₁ closedp = subst Last (sym (closed-stuck closedp path)) lp closedq
  ... | inj₂ open′ = inj₁ (lower (λ closedp → ⊥-elim (open′ closedp)) closedq)

-- Exit-wrapper coordinator calls; only finishClose can close.
control-frame : ∀ a s {t} → W.control a s ≡ just t → Frame (W.shutdown s) (W.shutdown t)
control-frame Close.finishClose s eq with EF.control-observation Close.finishClose s eq
... | EF.control pc stepped refl = frame ((Close.finishClose ∷ []) ,
  Close.next {current = Shared.cm (W.shared s)} {available = λ w → W.resultReady w s} stepped Close.done)
  (λ _ _ → inj₂ (exitWait s _ eq refl (Handler.make-wait (Shared.cm (W.shared s)) (λ w → W.resultReady w s) (W.shutdown s) stepped) refl))
control-frame Close.captureSnapshot s eq with EF.control-observation Close.captureSnapshot s eq
... | EF.control pc stepped refl = step-frame (Shared.cm (W.shared s)) (λ w → W.resultReady w s) Close.captureSnapshot (W.shutdown s) stepped (λ ())
control-frame Close.readEntry s eq with EF.control-observation Close.readEntry s eq
... | EF.control pc stepped refl = step-frame (Shared.cm (W.shared s)) (λ w → W.resultReady w s) Close.readEntry (W.shutdown s) stepped (λ ())
control-frame Close.requestCancellation s eq with EF.control-observation Close.requestCancellation s eq
... | EF.control pc stepped refl = step-frame (Shared.cm (W.shared s)) (λ w → W.resultReady w s) Close.requestCancellation (W.shutdown s) stepped (λ ())
control-frame Close.acknowledgeDelivery s eq with EF.control-observation Close.acknowledgeDelivery s eq
... | EF.control pc stepped refl = step-frame (Shared.cm (W.shared s)) (λ w → W.resultReady w s) Close.acknowledgeDelivery (W.shutdown s) stepped (λ ())
control-frame Close.finishTraversal s eq with EF.control-observation Close.finishTraversal s eq
... | EF.control pc stepped refl = step-frame (Shared.cm (W.shared s)) (λ w → W.resultReady w s) Close.finishTraversal (W.shutdown s) stepped (λ ())

-- Mux handler supervision: its projected coordinator path.
mux-frame : ∀ a s {t} → U.step a s ≡ just t → Frame (B.shutdown (U.base s)) (B.shutdown (U.base t))
mux-frame a s eq = from-handler (UF.coordinator projected) (UF.last-wait projected)
  where projected = UF.step-projects a s eq

coordP : P.State → Close.State
coordP s = B.shutdown (U.base (P.base s))
protocol-frame : ∀ a s {t} → P.step a s ≡ just t → Frame (coordP s) (coordP t)
protocol-frame (P.run a) s eq with P.inheritedAllowed a
... | false = case eq of λ ()
... | true with U.step a (P.base s) in actual
...   | nothing = case eq of λ ()
...   | just u = case just-injective eq of λ { refl → mux-frame a (P.base s) actual }
protocol-frame (P.forkResponder w j gen) s eq = same (Aux.Protocol.direct-shutdown-same (P.forkResponder w j gen) s eq tt)
protocol-frame (P.forkInitiator w j gen n) s eq = same (Aux.Protocol.direct-shutdown-same (P.forkInitiator w j gen n) s eq tt)
protocol-frame (P.registerProtocol j) s eq = same (Aux.Protocol.direct-shutdown-same (P.registerProtocol j) s eq tt)
protocol-frame (P.enterProtocolBody j) s eq = same (Aux.Protocol.direct-shutdown-same (P.enterProtocolBody j) s eq tt)
protocol-frame (P.appendProtocolPayload j bytes) s eq = same (Aux.Protocol.direct-shutdown-same (P.appendProtocolPayload j bytes) s eq tt)
protocol-frame (P.egressMuxer w action) s eq = same (Aux.Protocol.direct-shutdown-same (P.egressMuxer w action) s eq tt)
protocol-frame (P.protocolReturned j) s eq = same (Aux.Protocol.direct-shutdown-same (P.protocolReturned j) s eq tt)
protocol-frame (P.commitClean j) s eq = same (Aux.Protocol.direct-shutdown-same (P.commitClean j) s eq tt)
protocol-frame (P.protocolException j err) s eq = same (Aux.Protocol.direct-shutdown-same (P.protocolException j err) s eq tt)
protocol-frame (P.returnProtocol j) s eq = same (Aux.Protocol.direct-shutdown-same (P.returnProtocol j) s eq tt)
protocol-frame (P.publishProtocol j) s eq = same (Aux.Protocol.direct-shutdown-same (P.publishProtocol j) s eq tt)
protocol-frame (P.deregisterProtocol j) s eq = same (Aux.Protocol.direct-shutdown-same (P.deregisterProtocol j) s eq tt)
protocol-frame (P.asyncProtocolResult j) s eq = same (Aux.Protocol.direct-shutdown-same (P.asyncProtocolResult j) s eq tt)
protocol-frame (P.infrastructureReturn w role err) s eq = same (Aux.Protocol.direct-shutdown-same (P.infrastructureReturn w role err) s eq tt)
protocol-frame (P.publishInfra w role) s eq = same (Aux.Protocol.direct-shutdown-same (P.publishInfra w role) s eq tt)
protocol-frame (P.deregisterInfra w role) s eq = same (Aux.Protocol.direct-shutdown-same (P.deregisterInfra w role) s eq tt)
protocol-frame (P.asyncInfraResult w role) s eq = same (Aux.Protocol.direct-shutdown-same (P.asyncInfraResult w role) s eq tt)
protocol-frame (P.control w action) s eq = same (Aux.Protocol.direct-shutdown-same (P.control w action) s eq tt)
protocol-frame (P.submitDbWrite j d) s eq = same (Aux.Protocol.direct-shutdown-same (P.submitDbWrite j d) s eq tt)
protocol-frame (P.awaitDbWrite j) s eq = same (Aux.Protocol.direct-shutdown-same (P.awaitDbWrite j) s eq tt)
protocol-frame (P.dbWriteFailed j) s eq = same (Aux.Protocol.direct-shutdown-same (P.dbWriteFailed j) s eq tt)
protocol-frame (P.writerComplete d) s eq = same (Aux.Protocol.direct-shutdown-same (P.writerComplete d) s eq tt)
protocol-frame (P.writerSeal err) s eq = same (Aux.Protocol.direct-shutdown-same (P.writerSeal err) s eq tt)

coordM : M.State → Close.State
coordM s = coordP (M.base s)
monitor-frame : ∀ a s {t} → M.step a s ≡ just t → Frame (coordM s) (coordM t)
monitor-frame (M.run a) s eq with M.delegateAllowed a s
... | false = case eq of λ ()
... | true with P.step a (M.base s) in actual
...   | nothing = case eq of λ ()
...   | just lower = case just-injective eq of λ { refl → protocol-frame a (M.base s) actual }
monitor-frame (M.consume w) s eq = same (Aux.Monitor.direct-shutdown-same isBearerClosed (M.consume w) s eq tt)
monitor-frame (M.handleSelected w) s eq = same (Aux.Monitor.direct-shutdown-same isBearerClosed (M.handleSelected w) s eq tt)
monitor-frame (M.sampleTracer w) s eq = same (Aux.Monitor.direct-shutdown-same isBearerClosed (M.sampleTracer w) s eq tt)
monitor-frame (M.commitTracer w) s eq = same (Aux.Monitor.direct-shutdown-same isBearerClosed (M.commitTracer w) s eq tt)
monitor-frame (M.finishProtocolTrace w) s eq = same (Aux.Monitor.direct-shutdown-same isBearerClosed (M.finishProtocolTrace w) s eq tt)
monitor-frame (M.beginDead w) s eq = same (Aux.Monitor.direct-shutdown-same isBearerClosed (M.beginDead w) s eq tt)
monitor-frame (M.finishDead w) s eq = same (Aux.Monitor.direct-shutdown-same isBearerClosed (M.finishDead w) s eq tt)

coordG : G.State → Close.State
coordG s = coordM (G.base s)
group-frame : ∀ a s {t} → G.step a s ≡ just t → Frame (coordG s) (coordG t)
group-frame (G.run a) s eq with G.delegateAllowed a s
... | false = case eq of λ ()
... | true with M.step a (G.base s) in actual
...   | nothing = case eq of λ ()
...   | just lower = case just-injective eq of λ { refl → monitor-frame a (G.base s) actual }
group-frame (G.requestShutdown w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.requestShutdown w) s eq tt)
group-frame (G.retireCounters w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.retireCounters w) s eq tt)
group-frame (G.selectShutdown w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.selectShutdown w) s eq tt)
group-frame (G.observeStoppingTrace w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.observeStoppingTrace w) s eq tt)
group-frame (G.writeStopping w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.writeStopping w) s eq tt)
group-frame (G.captureGroup w order) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.captureGroup w order) s eq tt)
group-frame (G.requestGroupCancel w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.requestGroupCancel w) s eq tt)
group-frame (G.deliverGroup w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.deliverGroup w) s eq tt)
group-frame (G.joinGroup w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.joinGroup w) s eq tt)
group-frame (G.finishGroup w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.finishGroup w) s eq tt)
group-frame (G.drainEmpty w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.drainEmpty w) s eq tt)
group-frame (G.timeout2Elapsed w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.timeout2Elapsed w) s eq tt)
group-frame (G.writeStopped w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.writeStopped w) s eq tt)
group-frame (G.observeTraceStopped w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.observeTraceStopped w) s eq tt)
group-frame (G.sampleStoppedTracer w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.sampleStoppedTracer w) s eq tt)
group-frame (G.commitStoppedTracer w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.commitStoppedTracer w) s eq tt)
group-frame (G.finishStoppedTrace w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.finishStoppedTrace w) s eq tt)
group-frame (G.finishChildUnwind j) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.finishChildUnwind j) s eq tt)
group-frame (G.unwindReplacedBySync j err) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.unwindReplacedBySync j err) s eq tt)
group-frame (G.abortOwner w err) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.abortOwner w err) s eq tt)
group-frame (G.beginWholeClose w order) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.beginWholeClose w order) s eq tt)
group-frame (G.requestWholeCancel w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.requestWholeCancel w) s eq tt)
group-frame (G.deliverWhole w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.deliverWhole w) s eq tt)
group-frame (G.joinWhole w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.joinWhole w) s eq tt)
group-frame (G.finishWholeClose w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.finishWholeClose w) s eq tt)
group-frame (G.finishNormalScope w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.finishNormalScope w) s eq tt)
group-frame (G.writeAsyncFailure w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.writeAsyncFailure w) s eq tt)
group-frame (G.beginAsyncDead w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.beginAsyncDead w) s eq tt)
group-frame (G.sampleAsyncTracer w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.sampleAsyncTracer w) s eq tt)
group-frame (G.commitAsyncTracer w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.commitAsyncTracer w) s eq tt)
group-frame (G.finishAsyncDead w) s eq = same (Aux.Group.direct-shutdown-same isBearerClosed (G.finishAsyncDead w) s eq tt)

-- Exit wrapper: plans either keep the coordinator, run a group step, or call
-- the coordinator through the wrapper's own result table.
exit-enact-frame : ∀ plan s {t} → W.enact plan s ≡ just t → Frame (W.shutdown s) (W.shutdown t)
exit-enact-frame (W.local fs) s eq = case just-injective eq of λ { refl → stay _ }
exit-enact-frame (W.machine action fs) s eq with O.advance action (W.source s)
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → stay _ }
exit-enact-frame (W.inherited action) s eq with G.step action (W.base s) in advanced
... | nothing = case eq of λ ()
... | just g = case just-injective eq of λ { refl → group-frame action (W.base s) advanced }
exit-enact-frame (W.coordinator action) s eq = control-frame action s eq
exit-enact-frame (W.handshakeDelivery w window err) s eq with G.step (W.handshakeAction w window err) (W.base s) in advanced
... | nothing = case eq of λ ()
... | just g = compose (group-frame (W.handshakeAction w window err) (W.base s) advanced)
  (control-frame Close.acknowledgeDelivery (record s { base = g }) eq)
exit-enact-frame (W.muxDelivery w err) s eq with G.step (G.abortOwner w err) (W.base s) in advanced
... | nothing = case eq of λ ()
... | just g = compose (group-frame (G.abortOwner w err) (W.base s) advanced)
  (control-frame Close.acknowledgeDelivery (record s { base = g }) eq)
exit-enact-frame (W.timeWaitDelivery w err) s eq with O.advance (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s)
... | nothing = case eq of λ ()
... | just c = control-frame Close.acknowledgeDelivery (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq
exit-enact-frame (W.releaseDelivery caller target err) s eq with G.step (G.abortOwner target err) (W.base s) in aborted
... | nothing = case eq of λ ()
... | just g with O.advance (O.release caller (Release.cancellationDelivered target)) (G.source g)
...   | nothing = case eq of λ ()
...   | just c = case just-injective eq of λ { refl → group-frame (G.abortOwner target err) (W.base s) aborted }
exit-enact-frame (W.releaseTimeWaitDelivery caller target err) s eq with O.advance (O.inbound (Machine.cleanupStep target (Cleanup.interruptTimeWait err))) (W.source s)
... | nothing = case eq of λ ()
... | just c with O.advance (O.release caller (Release.cancellationDelivered target)) c
...   | nothing = case eq of λ ()
...   | just c′ = case just-injective eq of λ { refl → stay _ }
exit-frame : ∀ a s {t} → W.step a s ≡ just t → Frame (W.shutdown s) (W.shutdown t)
exit-frame a s eq with W.choose a s
... | nothing = case eq of λ ()
... | just plan = exit-enact-frame plan s eq

-- Cancellation delivery: exit-frame edits plus one acknowledgment.
cancellation-frame : ∀ a s {t} → X.step a s ≡ just t → Frame (W.shutdown s) (W.shutdown t)
cancellation-frame (X.run a) s eq = exit-frame a s eq
cancellation-frame (X.observeCancellation window w err) s eq with lookup w (W.exits s)
... | nothing = case eq of λ ()
... | just f with X.target window err (W.phase f)
...   | nothing = case eq of λ ()
...   | just pc = case just-injective eq of λ { refl → stay _ }
cancellation-frame (X.observeErrorTraceException w err) s eq with lookup w (W.exits s)
... | nothing = case eq of λ ()
... | just f with W.phase f
...   | W.errorTracing _ _ = case just-injective eq of λ { refl → stay _ }
...   | W.bufferScope _ = case eq of λ ()
...   | W.classifying _ = case eq of λ ()
...   | W.peerRethrow _ = case eq of λ ()
...   | W.nodeDelivery _ = case eq of λ ()
...   | W.nodeRethrow _ = case eq of λ ()
...   | W.bodyExited _ = case eq of λ ()
...   | W.finalizing _ = case eq of λ ()
...   | W.cleanupComplete _ _ = case eq of λ ()
...   | W.resultAvailable _ _ = case eq of λ ()
cancellation-frame (X.deliverShutdown window err) s eq with Close.phase (W.shutdown s)
... | Close.awaitDelivery e w with X.deliver window w err s in delivered
...   | nothing = case eq of λ ()
...   | just next = compose (deliver-same delivered) (control-frame Close.acknowledgeDelivery next eq)
  where
  deliver-same : ∀ {next} → X.deliver window w err s ≡ just next → Frame (W.shutdown s) (W.shutdown next)
  deliver-same d with lookup w (W.exits s)
  ... | nothing = case d of λ ()
  ... | just f with X.target window err (W.phase f)
  ...   | nothing = case d of λ ()
  ...   | just pc = case just-injective d of λ { refl → stay _ }
cancellation-frame (X.deliverShutdown window err) s eq | Close.initial = case eq of λ ()
cancellation-frame (X.deliverShutdown window err) s eq | Close.reading = case eq of λ ()
cancellation-frame (X.deliverShutdown window err) s eq | Close.sendReady _ _ = case eq of λ ()
cancellation-frame (X.deliverShutdown window err) s eq | Close.awaitResults = case eq of λ ()
cancellation-frame (X.deliverShutdown window err) s eq | Close.closed = case eq of λ ()

-- Startup unwind plans, including an acknowledged delivery.
coordR : R.State → Close.State
coordR s = W.shutdown (R.base s)
unwind-enact-frame : ∀ plan s {t} → R.enact plan s ≡ just t → Frame (coordR s) (coordR t)
unwind-enact-frame (R.local fs) s eq = case just-injective eq of λ { refl → stay _ }
unwind-enact-frame (R.machine action fs) s eq with O.advance action (R.source s)
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → stay _ }
unwind-enact-frame (R.pool w u action fs) s eq with G.Pool.step action (R.poolAt w s)
... | nothing = case eq of λ ()
... | just p = case just-injective eq of λ { refl → stay _ }
unwind-enact-frame (R.inherited action) s eq with X.step action (R.base s) in advanced
... | nothing = case eq of λ ()
... | just x = case just-injective eq of λ { refl → cancellation-frame action (R.base s) advanced }
unwind-enact-frame (R.transfer w f fs) s eq = case just-injective eq of λ { refl → stay _ }
unwind-enact-frame (R.acknowledge plan) s eq with R.enact plan s in delivered
... | nothing = case eq of λ ()
... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
...   | nothing = case eq of λ ()
...   | just x = case just-injective eq of λ { refl → compose (unwind-enact-frame plan s delivered)
  (control-frame Close.acknowledgeDelivery (R.base next) acknowledged) }
unwind-frame : ∀ a s {t} → R.step a s ≡ just t → Frame (coordR s) (coordR t)
unwind-frame a s eq with R.choose a s
... | nothing = case eq of λ ()
... | just plan = unwind-enact-frame plan s eq

-- DeltaQ callbacks: ticket metadata, inherited unwind steps, or one plan.
coordD : D.State → Close.State
coordD s = coordR (D.base s)
delta-apply-frame : ∀ w plan ack s {t} → D.applyFault w plan ack s ≡ just t → Frame (coordD s) (coordD t)
delta-apply-frame w plan ack s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with R.enact (D.delivery ack plan) (D.base s) in advanced
...   | nothing = case eq of λ ()
...   | just r = case just-injective eq of λ { refl → unwind-enact-frame (D.delivery ack plan) (D.base s) advanced }
delta-throw-frame : ∀ w result ack s {t} → D.throw w result ack s ≡ just t → Frame (coordD s) (coordD t)
delta-throw-frame w result ack s eq with D.faultPlan w result s
... | nothing = case eq of λ ()
... | just plan = delta-apply-frame w plan ack s eq
delta-throw-initiator-frame : ∀ w result ack s {t} → D.throwInitiator w result ack s ≡ just t → Frame (coordD s) (coordD t)
delta-throw-initiator-frame w result ack s eq with D.initiatorFaultPlan w result s
... | nothing = case eq of λ ()
... | just plan = delta-apply-frame w plan ack s eq
delta-frame : ∀ a s {t} → D.step a s ≡ just t → Frame (coordD s) (coordD t)
delta-frame (D.run action) s eq with D.allowed action s
... | false = case eq of λ ()
... | true with R.step action (D.base s) in advanced
...   | nothing = case eq of λ ()
...   | just r = case just-injective eq of λ { refl → unwind-frame action (D.base s) advanced }
delta-frame (D.beginDeltaQ w) s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.entryPhase t ∧ D.ready w t s
...   | true = case just-injective eq of λ { refl → stay _ }
...   | false = case eq of λ ()
delta-frame (D.observeReturn w) s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.phase t | D.ready w t s
...   | D.invoked | true with R.step (D.finishAction w (D.payload t)) (D.base s) in advanced
...     | nothing = case eq of λ ()
...     | just r = case just-injective eq of λ { refl → unwind-frame (D.finishAction w (D.payload t)) (D.base s) advanced }
delta-frame (D.observeReturn w) s eq | just t | D.captured | _ = case eq of λ ()
delta-frame (D.observeReturn w) s eq | just t | D.muxInvoked | _ = case eq of λ ()
delta-frame (D.observeReturn w) s eq | just t | D.muxReturned | _ = case eq of λ ()
delta-frame (D.observeReturn w) s eq | just t | D.returned | _ = case eq of λ ()
delta-frame (D.observeReturn w) s eq | just t | D.throwing | _ = case eq of λ ()
delta-frame (D.observeReturn w) s eq | just t | D.invoked | false = case eq of λ ()
delta-frame (D.observeException w err) s eq = delta-throw-frame w err false s eq
delta-frame (D.beginInitiatorTrace w) s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.phase t | D.initiatorReady w t s
...   | D.captured | true = case just-injective eq of λ { refl → stay _ }
...   | D.captured | false = case eq of λ ()
...   | D.muxInvoked | _ = case eq of λ ()
...   | D.muxReturned | _ = case eq of λ ()
...   | D.invoked | _ = case eq of λ ()
...   | D.returned | _ = case eq of λ ()
...   | D.throwing | _ = case eq of λ ()
delta-frame (D.observeInitiatorReturn w) s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.phase t | D.initiatorReady w t s
...   | D.muxInvoked | true with D.payload t
...     | Types.protocolCompletion Mux.initiatorJob n gen clean = case just-injective eq of λ { refl → stay _ }
...     | Types.protocolCompletion Mux.initiatorJob n gen (errored err) with R.step (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) in advanced
...       | nothing = case eq of λ ()
...       | just r = case just-injective eq of λ { refl → unwind-frame (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) advanced }
delta-frame (D.observeInitiatorReturn w) s eq | just t | D.muxInvoked | true | Types.protocolCompletion Mux.responderJob n gen outcome = case eq of λ ()
delta-frame (D.observeInitiatorReturn w) s eq | just t | D.muxInvoked | true | Types.infraMuxer err = case eq of λ ()
delta-frame (D.observeInitiatorReturn w) s eq | just t | D.muxInvoked | true | Types.infraDemuxer err = case eq of λ ()
delta-frame (D.observeInitiatorReturn w) s eq | just t | D.muxInvoked | false = case eq of λ ()
delta-frame (D.observeInitiatorReturn w) s eq | just t | D.captured | _ = case eq of λ ()
delta-frame (D.observeInitiatorReturn w) s eq | just t | D.muxReturned | _ = case eq of λ ()
delta-frame (D.observeInitiatorReturn w) s eq | just t | D.invoked | _ = case eq of λ ()
delta-frame (D.observeInitiatorReturn w) s eq | just t | D.returned | _ = case eq of λ ()
delta-frame (D.observeInitiatorReturn w) s eq | just t | D.throwing | _ = case eq of λ ()
delta-frame (D.observeInitiatorException w err) s eq = delta-throw-initiator-frame w err false s eq
delta-frame (D.deliverShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
... | Close.awaitDelivery e w = delta-throw-frame w (R.async err) true s eq
... | Close.initial = case eq of λ ()
... | Close.reading = case eq of λ ()
... | Close.sendReady e w = case eq of λ ()
... | Close.awaitResults = case eq of λ ()
... | Close.closed = case eq of λ ()
delta-frame (D.deliverInitiatorShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
... | Close.awaitDelivery e w = delta-throw-initiator-frame w (R.async err) true s eq
... | Close.initial = case eq of λ ()
... | Close.reading = case eq of λ ()
... | Close.sendReady e w = case eq of λ ()
... | Close.awaitResults = case eq of λ ()
... | Close.closed = case eq of λ ()

-- Catch adapter.
coordC : C.State → Close.State
coordC s = coordD (C.base s)
catch-observe-frame : ∀ w reason ack s {t} → C.observe w reason ack s ≡ just t → Frame (coordC s) (coordC t)
catch-observe-frame w reason ack s eq with C.select w reason s
... | nothing = case eq of λ ()
... | just p with R.enact (D.delivery ack (C.action p)) (D.base (C.base s)) in advanced
...   | nothing = case eq of λ ()
...   | just r = case just-injective eq of λ { refl → unwind-enact-frame (D.delivery ack (C.action p)) (D.base (C.base s)) advanced }
catch-frame : ∀ a s {t} → C.step a s ≡ just t → Frame (coordC s) (coordC t)
catch-frame (C.run action) s eq with C.allowed action
... | false = case eq of λ ()
... | true with D.step action (C.base s) in advanced
...   | nothing = case eq of λ ()
...   | just d = case just-injective eq of λ { refl → delta-frame action (C.base s) advanced }
catch-frame (C.observeException w err) s eq = catch-observe-frame w (C.synchronous err) false s eq
catch-frame (C.observeCancellation w site err) s eq = catch-observe-frame w (C.cancellation site err) false s eq
catch-frame (C.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base (D.base (C.base s))))
... | Close.awaitDelivery _ w = catch-observe-frame w (C.cancellation site err) true s eq
... | Close.initial = case eq of λ ()
... | Close.reading = case eq of λ ()
... | Close.sendReady _ _ = case eq of λ ()
... | Close.awaitResults = case eq of λ ()
... | Close.closed = case eq of λ ()

-- Publication unwind: the coordinator read by the Server layer.
coordN : N.State → Close.State
coordN s = W.shutdown (R.base (N.raw s))
publication-observe-frame : ∀ w site result ack s {t} → N.observe w site result ack s ≡ just t → Frame (coordN s) (coordN t)
publication-observe-frame w site result ack s eq with N.select w site result s
... | nothing = case eq of λ ()
... | just p with R.enact (D.delivery ack (N.action p)) (N.raw s) in advanced
...   | nothing = case eq of λ ()
...   | just r = case just-injective eq of λ { refl → unwind-enact-frame (D.delivery ack (N.action p)) (N.raw s) advanced }
publication-frame : ∀ a s {t} → N.step a s ≡ just t → Frame (coordN s) (coordN t)
publication-frame (N.run action) s eq with N.allowed action s
... | false = case eq of λ ()
... | true with C.step action (N.base s) in advanced
...   | nothing = case eq of λ ()
...   | just c = case just-injective eq of λ { refl → catch-frame action (N.base s) advanced }
publication-frame (N.observeFailure w site result) s eq = publication-observe-frame w site result false s eq
publication-frame (N.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base (N.raw s)))
... | Close.awaitDelivery _ w = publication-observe-frame w site (R.async err) true s eq
... | Close.initial = case eq of λ ()
... | Close.reading = case eq of λ ()
... | Close.sendReady _ _ = case eq of λ ()
... | Close.awaitResults = case eq of λ ()
... | Close.closed = case eq of λ ()
