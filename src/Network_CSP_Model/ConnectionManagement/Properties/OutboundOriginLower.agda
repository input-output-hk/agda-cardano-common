{-# OPTIONS --guardedness #-}

-- Active-acquisition effects through actual physical/mux wrapper steps.
-- Handler-only and direct mux effects preserve the acquisition runtime.
module ConnectionManagement.Properties.OutboundOriginLower where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import ConnectionManagement.Domain using (ErrorId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.OutboundRelease as Release
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxExitCancellation as CancellationModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Properties.OutboundOriginQuiet as Quiet
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.OutboundAcquire as Acquire
open import ConnectionManagement.Properties.OutboundOriginEffect using (Effect; same; reframe; outbound-effect)

module Physical where
 fork-effect : ∀ w s {t} → B.forkOutbound w s ≡ just t → Effect (B.source s) (B.source t)
 fork-effect w s eq with lookup w (O.acquiring (B.source s))
 ... | nothing = case eq of λ ()
 ... | just f with B.freshChild (Acquire.child (Acquire.req f)) s
 ...   | false = case eq of λ ()
 ...   | true with O.advance (O.acquire w Acquire.forkOK) (B.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (Acquire.child (Acquire.req f)) (Shared.handlers (Machine.world (O.core c)))
 ...       | nothing = case eq of λ ()
 ...       | just captured = case just-injective eq of λ { refl → outbound-effect (O.acquire w Acquire.forkOK) (B.source s) actual }
 effect : ∀ action s {t} → B.step action s ≡ just t → Effect (B.source s) (B.source t)
 effect (B.handler action) s eq with B.handlerAllowed action s
 ... | false = case eq of λ ()
 ... | true with H.step action (B.view s)
 ...   | nothing = case eq of λ ()
 ...   | just h = case just-injective eq of λ { refl → same refl }
 effect (B.outbound action) s eq with B.forkCaller action
 ... | just w = fork-effect w s eq
 ... | nothing with B.outboundAllowed action s
 ...   | false = case eq of λ ()
 ...   | true with O.advance action (B.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → outbound-effect action (B.source s) actual }

module Mux where
 private module U = MuxModel Types.TypedResult using (Action; source; State; allocateHandle; base; baseAllowed; birth; birthFresh; initial; negotiate; noteBirth; origins; publishSuccess; run; startupStep; step)
 note-source : ∀ origin s → U.source (U.noteBirth origin s) ≡ U.source s
 note-source nothing s = refl
 note-source (just origin) s = refl
 effect : ∀ a s {t} → U.step a s ≡ just t → Effect (U.source s) (U.source t)
 effect (U.run a) s eq with U.baseAllowed a s ∧ U.birthFresh (U.birth a (U.base s)) (U.origins s)
 ... | false = case eq of λ ()
 ... | true with B.step a (U.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just b = case just-injective eq of λ { refl → reframe refl (note-source (U.birth a (U.base s)) (record s { base = b })) (Physical.effect a (U.base s) actual) }
 effect (U.negotiate w ps flow) s eq = same (Quiet.Mux.direct-same (U.negotiate w ps flow) s eq tt)
 effect (U.allocateHandle w hid mid) s eq = same (Quiet.Mux.direct-same (U.allocateHandle w hid mid) s eq tt)
 effect (U.publishSuccess w) s eq = same (Quiet.Mux.direct-same (U.publishSuccess w) s eq tt)
 effect (U.startupStep w action) s eq = same (Quiet.Mux.direct-same (U.startupStep w action) s eq tt)

module Protocol where
 private module P = ProtocolModel using (Action; source; State; enterProtocolBody; appendProtocolPayload; egressMuxer; asyncInfraResult; asyncProtocolResult; base; commitClean; control; deregisterInfra; deregisterProtocol; forkInitiator; forkResponder; infrastructureReturn; inheritedAllowed; initial; protocolException; protocolReturned; publishInfra; publishProtocol; registerProtocol; returnProtocol; run; step)
 private module U = MuxModel Types.TypedResult using (step)
 effect : ∀ a s {t} → P.step a s ≡ just t → Effect (P.source s) (P.source t)
 effect (P.run a) s eq with P.inheritedAllowed a
 ... | false = case eq of λ ()
 ... | true with U.step a (P.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just u = case just-injective eq of λ { refl → Mux.effect a (P.base s) actual }
 effect (P.forkResponder w j gen) s eq = same (Quiet.Protocol.direct-same (P.forkResponder w j gen) s eq tt)
 effect (P.forkInitiator w j gen n) s eq = same (Quiet.Protocol.direct-same (P.forkInitiator w j gen n) s eq tt)
 effect (P.registerProtocol j) s eq = same (Quiet.Protocol.direct-same (P.registerProtocol j) s eq tt)
 -- M1 egress writers update only the actual IG mux egress cell.
 effect (P.enterProtocolBody j) s eq = same (Quiet.Protocol.direct-same (P.enterProtocolBody j) s eq tt)
 effect (P.appendProtocolPayload j bytes) s eq = same (Quiet.Protocol.direct-same (P.appendProtocolPayload j bytes) s eq tt)
 effect (P.egressMuxer w action) s eq = same (Quiet.Protocol.direct-same (P.egressMuxer w action) s eq tt)
 effect (P.protocolReturned j) s eq = same (Quiet.Protocol.direct-same (P.protocolReturned j) s eq tt)
 effect (P.commitClean j) s eq = same (Quiet.Protocol.direct-same (P.commitClean j) s eq tt)
 effect (P.protocolException j err) s eq = same (Quiet.Protocol.direct-same (P.protocolException j err) s eq tt)
 effect (P.returnProtocol j) s eq = same (Quiet.Protocol.direct-same (P.returnProtocol j) s eq tt)
 effect (P.publishProtocol j) s eq = same (Quiet.Protocol.direct-same (P.publishProtocol j) s eq tt)
 effect (P.deregisterProtocol j) s eq = same (Quiet.Protocol.direct-same (P.deregisterProtocol j) s eq tt)
 effect (P.asyncProtocolResult j) s eq = same (Quiet.Protocol.direct-same (P.asyncProtocolResult j) s eq tt)
 effect (P.infrastructureReturn w role err) s eq = same (Quiet.Protocol.direct-same (P.infrastructureReturn w role err) s eq tt)
 effect (P.publishInfra w role) s eq = same (Quiet.Protocol.direct-same (P.publishInfra w role) s eq tt)
 effect (P.deregisterInfra w role) s eq = same (Quiet.Protocol.direct-same (P.deregisterInfra w role) s eq tt)
 effect (P.asyncInfraResult w role) s eq = same (Quiet.Protocol.direct-same (P.asyncInfraResult w role) s eq tt)
 effect (P.control w action) s eq = same (Quiet.Protocol.direct-same (P.control w action) s eq tt)

module Monitor (b : ErrorId → Bool) where
 private module M = MonitorModel b using (Action; source; State; base; beginDead; commitTracer; consume; delegateAllowed; finishDead; finishProtocolTrace; handleSelected; initial; run; sampleTracer; step)
 private module P = ProtocolModel using (step)
 effect : ∀ a s {t} → M.step a s ≡ just t → Effect (M.source s) (M.source t)
 effect (M.run a) s eq with M.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with P.step a (M.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just lower = case just-injective eq of λ { refl → Protocol.effect a (M.base s) actual }
 effect (M.consume w) s eq = same (Quiet.Monitor.direct-same b (M.consume w) s eq tt)
 effect (M.handleSelected w) s eq = same (Quiet.Monitor.direct-same b (M.handleSelected w) s eq tt)
 effect (M.sampleTracer w) s eq = same (Quiet.Monitor.direct-same b (M.sampleTracer w) s eq tt)
 effect (M.commitTracer w) s eq = same (Quiet.Monitor.direct-same b (M.commitTracer w) s eq tt)
 effect (M.finishProtocolTrace w) s eq = same (Quiet.Monitor.direct-same b (M.finishProtocolTrace w) s eq tt)
 effect (M.beginDead w) s eq = same (Quiet.Monitor.direct-same b (M.beginDead w) s eq tt)
 effect (M.finishDead w) s eq = same (Quiet.Monitor.direct-same b (M.finishDead w) s eq tt)

module Group (b : ErrorId → Bool) where
 private module G = GroupModel b using (Action; source; State; abortOwner; base; beginAsyncDead; beginWholeClose; captureGroup; commitAsyncTracer; commitStoppedTracer; delegateAllowed; deliverGroup; deliverWhole; drainEmpty; finishAsyncDead; finishChildUnwind; finishGroup; finishNormalScope; finishStoppedTrace; finishWholeClose; initial; joinGroup; joinWhole; observeStoppingTrace; observeTraceStopped; requestGroupCancel; requestShutdown; requestWholeCancel; run; sampleAsyncTracer; sampleStoppedTracer; selectShutdown; step; timeout2Elapsed; unwindReplacedBySync; writeAsyncFailure; writeStopped; writeStopping)
 private module M = MonitorModel b using (step)
 effect : ∀ a s {t} → G.step a s ≡ just t → Effect (G.source s) (G.source t)
 effect (G.run a) s eq with G.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with M.step a (G.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just lower = case just-injective eq of λ { refl → Monitor.effect b a (G.base s) actual }
 effect (G.requestShutdown w) s eq = same (Quiet.Group.direct-same b (G.requestShutdown w) s eq tt)
 effect (G.selectShutdown w) s eq = same (Quiet.Group.direct-same b (G.selectShutdown w) s eq tt)
 effect (G.observeStoppingTrace w) s eq = same (Quiet.Group.direct-same b (G.observeStoppingTrace w) s eq tt)
 effect (G.writeStopping w) s eq = same (Quiet.Group.direct-same b (G.writeStopping w) s eq tt)
 effect (G.captureGroup w order) s eq = same (Quiet.Group.direct-same b (G.captureGroup w order) s eq tt)
 effect (G.requestGroupCancel w) s eq = same (Quiet.Group.direct-same b (G.requestGroupCancel w) s eq tt)
 effect (G.deliverGroup w) s eq = same (Quiet.Group.direct-same b (G.deliverGroup w) s eq tt)
 effect (G.joinGroup w) s eq = same (Quiet.Group.direct-same b (G.joinGroup w) s eq tt)
 effect (G.finishGroup w) s eq = same (Quiet.Group.direct-same b (G.finishGroup w) s eq tt)
 effect (G.drainEmpty w) s eq = same (Quiet.Group.direct-same b (G.drainEmpty w) s eq tt)
 effect (G.timeout2Elapsed w) s eq = same (Quiet.Group.direct-same b (G.timeout2Elapsed w) s eq tt)
 effect (G.writeStopped w) s eq = same (Quiet.Group.direct-same b (G.writeStopped w) s eq tt)
 effect (G.observeTraceStopped w) s eq = same (Quiet.Group.direct-same b (G.observeTraceStopped w) s eq tt)
 effect (G.sampleStoppedTracer w) s eq = same (Quiet.Group.direct-same b (G.sampleStoppedTracer w) s eq tt)
 effect (G.commitStoppedTracer w) s eq = same (Quiet.Group.direct-same b (G.commitStoppedTracer w) s eq tt)
 effect (G.finishStoppedTrace w) s eq = same (Quiet.Group.direct-same b (G.finishStoppedTrace w) s eq tt)
 effect (G.finishChildUnwind j) s eq = same (Quiet.Group.direct-same b (G.finishChildUnwind j) s eq tt)
 effect (G.unwindReplacedBySync j err) s eq = same (Quiet.Group.direct-same b (G.unwindReplacedBySync j err) s eq tt)
 effect (G.abortOwner w err) s eq = same (Quiet.Group.direct-same b (G.abortOwner w err) s eq tt)
 effect (G.beginWholeClose w order) s eq = same (Quiet.Group.direct-same b (G.beginWholeClose w order) s eq tt)
 effect (G.requestWholeCancel w) s eq = same (Quiet.Group.direct-same b (G.requestWholeCancel w) s eq tt)
 effect (G.deliverWhole w) s eq = same (Quiet.Group.direct-same b (G.deliverWhole w) s eq tt)
 effect (G.joinWhole w) s eq = same (Quiet.Group.direct-same b (G.joinWhole w) s eq tt)
 effect (G.finishWholeClose w) s eq = same (Quiet.Group.direct-same b (G.finishWholeClose w) s eq tt)
 effect (G.finishNormalScope w) s eq = same (Quiet.Group.direct-same b (G.finishNormalScope w) s eq tt)
 effect (G.writeAsyncFailure w) s eq = same (Quiet.Group.direct-same b (G.writeAsyncFailure w) s eq tt)
 effect (G.beginAsyncDead w) s eq = same (Quiet.Group.direct-same b (G.beginAsyncDead w) s eq tt)
 effect (G.sampleAsyncTracer w) s eq = same (Quiet.Group.direct-same b (G.sampleAsyncTracer w) s eq tt)
 effect (G.commitAsyncTracer w) s eq = same (Quiet.Group.direct-same b (G.commitAsyncTracer w) s eq tt)
 effect (G.finishAsyncDead w) s eq = same (Quiet.Group.direct-same b (G.finishAsyncDead w) s eq tt)


module Exit (b : ErrorId → Bool) where
 private module W = ExitModel b using (State; Plan; source; base; setSource; control; shared; resultReady; shutdown; setShutdown; enact; local; machine; inherited; coordinator; muxDelivery; timeWaitDelivery; releaseDelivery; noteCleanup; step; choose)
 private module G = GroupModel b using (step; abortOwner; source)
 control-source : ∀ action s {t} → W.control action s ≡ just t → W.source t ≡ W.source s
 control-source action s eq with Close.step (Shared.cm (W.shared s)) (λ w → W.resultReady w s) action (W.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → refl }
 -- The real release acknowledgement changes caller/lifecycle bookkeeping,
 -- never the acquisition frames used by automatic outbound origin recovery.
 ack-acquiring : ∀ caller worker before {after} →
  O.advance (O.release caller (Release.cancellationDelivered worker)) before ≡ just after →
  O.acquiring after ≡ O.acquiring before
 ack-acquiring caller worker before actual with lookup caller (O.releasing before) |
  O.canDeliver (Release.cancellationDelivered worker) before
 ... | nothing | _ = case actual of λ ()
 ... | just saved | false = case actual of λ ()
 ... | just saved | true with Release.step (Machine.promotionHardLimit (O.core before))
  (Release.cancellationDelivered worker) saved (Machine.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (next , world) = case just-injective actual of λ { refl → refl }
 enact-effect : ∀ plan s {t} → W.enact plan s ≡ just t → Effect (W.source s) (W.source t)
 enact-effect (W.local fs) s eq = case just-injective eq of λ { refl → same refl }
 enact-effect (W.machine action fs) s eq with O.advance action (W.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → outbound-effect action (W.source s) actual }
 enact-effect (W.inherited action) s eq with G.step action (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl → Group.effect b action (W.base s) actual }
 enact-effect (W.coordinator action) s eq = same (cong O.acquiring (control-source action s eq))
 enact-effect (W.muxDelivery w err) s eq with G.step (G.abortOwner w err) (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = reframe refl (control-source Close.acknowledgeDelivery (record s { base = g }) eq)
   (Group.effect b (G.abortOwner w err) (W.base s) actual)
 enact-effect (W.timeWaitDelivery w err) s eq with O.advance (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = reframe refl (control-source Close.acknowledgeDelivery (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq)
   (outbound-effect (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s) actual)
 enact-effect (W.releaseDelivery caller worker err) s eq with G.step (G.abortOwner worker err) (W.base s) in aborted
 ... | nothing = case eq of λ ()
 ... | just g with O.advance (O.release caller (Release.cancellationDelivered worker)) (G.source g) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → same (trans
   (ack-acquiring caller worker (G.source g) acknowledged)
   (Quiet.Group.direct-same b (G.abortOwner worker err) (W.base s) aborted tt)) }
 effect : ∀ action s {t} → W.step action s ≡ just t → Effect (W.source s) (W.source t)
 effect action s eq with W.choose action s
 ... | nothing = case eq of λ ()
 ... | just plan = enact-effect plan s eq

module Cancellation (b : ErrorId → Bool) where
 private module X = CancellationModel b using (State; source; target; deliver; traceThrew; shutdownDelivery; step; run; observeCancellation; deliverShutdown; observeErrorTraceException)
 private module W = ExitModel b using (source; exits; phase; edit; bodyExited; syncException; bufferScope; classifying; errorTracing; peerRethrow; nodeDelivery; nodeRethrow; finalizing; cleanupComplete; resultAvailable; shutdown; control)
 deliver-source : ∀ window w err s {t} → X.deliver window w err s ≡ just t → X.source t ≡ X.source s
 deliver-source window w err s eq with lookup w (W.exits s)
 ... | nothing = case eq of λ ()
 ... | just f with X.target window err (W.phase f)
 ...   | nothing = case eq of λ ()
 ...   | just pc = case just-injective eq of λ { refl → refl }
 trace-source : ∀ w err s {t} → X.traceThrew w err s ≡ just t → X.source t ≡ X.source s
 trace-source w err s eq with lookup w (W.exits s)
 ... | nothing = case eq of λ ()
 ... | just f with W.phase f
 trace-source w err s eq | just f | W.bufferScope result = case eq of λ ()
 trace-source w err s eq | just f | W.classifying old = case eq of λ ()
 trace-source w err s eq | just f | W.errorTracing old policy = case just-injective eq of λ { refl → refl }
 trace-source w err s eq | just f | W.peerRethrow old = case eq of λ ()
 trace-source w err s eq | just f | W.nodeDelivery old = case eq of λ ()
 trace-source w err s eq | just f | W.nodeRethrow old = case eq of λ ()
 trace-source w err s eq | just f | W.bodyExited result = case eq of λ ()
 trace-source w err s eq | just f | W.finalizing result = case eq of λ ()
 trace-source w err s eq | just f | W.cleanupComplete result outcome = case eq of λ ()
 trace-source w err s eq | just f | W.resultAvailable result outcome = case eq of λ ()
 shutdown-source : ∀ window err s {t} → X.shutdownDelivery window err s ≡ just t → X.source t ≡ X.source s
 shutdown-source window err s eq with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with X.deliver window w err s in actual
 ...   | nothing = case eq of λ ()
 ...   | just next = trans (Exit.control-source b Close.acknowledgeDelivery next eq) (deliver-source window w err s actual)
 shutdown-source window err s eq | Close.initial = case eq of λ ()
 shutdown-source window err s eq | Close.reading = case eq of λ ()
 shutdown-source window err s eq | Close.sendReady e w = case eq of λ ()
 shutdown-source window err s eq | Close.awaitResults = case eq of λ ()
 shutdown-source window err s eq | Close.closed = case eq of λ ()
 effect : ∀ action s {t} → X.step action s ≡ just t → Effect (X.source s) (X.source t)
 effect (X.run action) s eq = Exit.effect b action s eq
 effect (X.observeCancellation window w err) s eq = same (cong O.acquiring (deliver-source window w err s eq))
 effect (X.deliverShutdown window err) s eq = same (cong O.acquiring (shutdown-source window err s eq))
 effect (X.observeErrorTraceException w err) s eq = same (cong O.acquiring (trace-source w err s eq))

module Unwind (b : ErrorId → Bool) where
 private module R = UnwindModel b using (source; base; faults; poolAt; setSource; setPool; enact; local; machine; pool; inherited; transfer; acknowledge; step; choose)
 private module X = CancellationModel b using (step)
 private module W = ExitModel b using (exits; control)
 private module G = GroupModel b using (module Pool)
 private module Pool = G.Pool using (step)
 enact-effect : ∀ plan s {t} → R.enact plan s ≡ just t → Effect (R.source s) (R.source t)
 enact-effect (R.local fs) s eq = case just-injective eq of λ { refl → same refl }
 enact-effect (R.machine action fs) s eq with O.advance action (R.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → outbound-effect action (R.source s) actual }
 enact-effect (R.pool w u action fs) s eq with Pool.step action (R.poolAt w s)
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → same refl }
 enact-effect (R.inherited action) s eq with X.step action (R.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Cancellation.effect b action (R.base s) actual }
 enact-effect (R.transfer w frame fs) s eq = case just-injective eq of λ { refl → same refl }
 enact-effect (R.acknowledge plan) s eq with R.enact plan s in actual
 ... | nothing = case eq of λ ()
 ... | just next with W.control Close.acknowledgeDelivery (R.base next) in controlled
 ...   | nothing = case eq of λ ()
 ...   | just x = case just-injective eq of λ { refl → reframe refl (Exit.control-source b Close.acknowledgeDelivery (R.base next) controlled) (enact-effect plan s actual) }
 effect : ∀ action s {t} → R.step action s ≡ just t → Effect (R.source s) (R.source t)
 effect action s eq with R.choose action s
 ... | nothing = case eq of λ ()
 ... | just plan = enact-effect plan s eq
