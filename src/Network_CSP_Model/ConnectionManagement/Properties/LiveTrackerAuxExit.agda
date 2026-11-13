{-# OPTIONS --guardedness #-}

-- Core/PC content and certified observers through exit and cancellation plans.
module ConnectionManagement.Properties.LiveTrackerAuxExit where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other; lookup-head)
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Properties.HandlerBirthEffects as Birth
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.OutboundRelease as OutboundRelease

import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.Rules.MuxRuntime as WireMux
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Properties.LiveTrackerAuxGroup as GroupFacts
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
import ConnectionManagement.Properties.LiveTrackerAuxProtocol as ProtocolFacts
import ConnectionManagement.Properties.LiveTrackerAuxMonitor as MonitorFacts

import ConnectionManagement.Properties.HandlerAuxBacking as Presence

import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.HandlerLifecycle as Life
module Exit (isBearerClosed : ErrorId → Bool)
 (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains isBearerClosed s t → Obs s → Obs t) where
 private module W = ExitModel isBearerClosed using (handshakeDelivery; handshakeAction; deliverShutdownHandshake; Action; Frame; Plan; State; acknowledgeFinished; acknowledgeReleaseFinished; deliverReleaseMux; deliverReleaseTimeWait; releaseTarget; timeWaitTarget; releaseDelivery; releaseTimeWaitDelivery; base; beginExit; bodyExited; bufferScope; choose; choosePolicy; classifying; cleanup; cleanupComplete; cleanupException; cleanupFault; control; coordinator; currentCapture; delegateAllowed; deliverShutdownMux; deliverShutdownTimeWait; edit; effectiveResult; enact; enterFinalizer; errorTracing; exits; finalizing; finishCleanup; inherited; initial; local; machine; muxDelivery; nodeDelivery; nodeRethrow; noteCleanup; observeBufferException; observeBufferReturn; observeErrorTrace; observeNodeDelivery; peerRethrow; phase; physical; poolAt; publishAsyncResult; resultAvailable; resultReady; rethrow; run; sameCleanup; sameStart; countersClear; setShutdown; setSource; shared; shutdown; shutdownStep; source; step; timeWaitDelivery)
 private module G = GroupModel isBearerClosed using (module M; base; abortOwner; asyncDeadTracing; asyncExit; asyncFailureWritten; drainReady; draining; failedExit; frameAt; groupClosing; idle; initial; monitorReturnedNormal; normalExit; ownerAborting; phase; protocolState; scopeDone; setPool; shutdownSelected; step; stoppedTrace; stoppedTracing; stoppingTraced; stoppingWritten; wholeClosed; wholeClosing)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base)
 private module U = P.U using (captured; frames)
 private module Pool = P.Pool using (step; cancelPending; closedPool; closing; joinPending; openPool; phase)
 private module Lower = GroupFacts.For isBearerClosed Obs stable using (Valid; source-valid; Observer; observer; step-preserves)
 private module Core = ProtocolFacts.For isBearerClosed
 private module Up = Updates isBearerClosed
 private module MF = MonitorFacts isBearerClosed
 Valid : W.State → Set
 Valid s = Lower.Valid (W.base s)
 source-valid : ∀ c s {as} → O.Executes (W.source s) as c → Valid s → Valid (W.setSource c s)
 source-valid c s path valid = Lower.source-valid c (W.base s) valid
 source-quiet : ∀ c s → Valid s → Valid (W.setSource c s)
 source-quiet c s = Lower.source-valid c (W.base s)
 shutdown-valid : ∀ coordinator s → Valid s → Valid (W.setShutdown coordinator s)
 shutdown-valid coordinator s = Core.same
   (Lower.Observer (G.M.pcs (G.base (W.base s)))) (Lower.observer _)
   (G.protocolState (W.base s)) (G.protocolState (W.base (W.setShutdown coordinator s))) refl refl (λ w → refl)
 control-preserves : ∀ a s {t} → W.control a s ≡ just t → Valid s → Valid t
 control-preserves a s eq valid with Close.step (S.cm (W.shared s)) (λ w → W.resultReady w s) a (W.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → shutdown-valid next s valid }
 -- Pool plans carry their actual current frame lookup and primitive step.
 pool-valid : ∀ w f a s {p} → lookup w (U.frames (P.base (G.protocolState (W.base s)))) ≡ just f →
   (actual : Pool.step a (W.poolAt w s) ≡ just p) → (∀ C → Up.Kernel.NewReturn a C) →
   Valid s → Valid (record s { base = G.setPool w f p (W.base s) })
 pool-valid w f a s found actual new = Core.pool-valid
   (Lower.Observer (G.M.pcs (G.base (W.base s)))) (Lower.observer _) w f a (G.protocolState (W.base s)) found actual (new _)
 -- Every exit plan preserves mux-frame content; exit records and cleanup
 -- bookkeeping are separate from the current immutable negotiation profile.
 enact-preserves : ∀ p s {t} → W.enact p s ≡ just t → Valid s → Valid t
 enact-preserves (W.local fs) s eq valid = case just-injective eq of λ { refl → valid }
 enact-preserves (W.machine a fs) s eq valid with O.advance a (W.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → source-valid c s (O.next {a = a} actual O.done) valid }
 enact-preserves (W.inherited a) s eq valid with G.step a (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl → Lower.step-preserves a (W.base s) actual valid }
 enact-preserves (W.coordinator a) s eq valid = control-preserves a s eq valid
 enact-preserves (W.handshakeDelivery w window err) s eq valid with G.step (W.handshakeAction w window err) (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = control-preserves Close.acknowledgeDelivery (record s { base = g }) eq
   (Lower.step-preserves (W.handshakeAction w window err) (W.base s) actual valid)
 enact-preserves (W.muxDelivery w err) s eq valid with G.step (G.abortOwner w err) (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = control-preserves Close.acknowledgeDelivery (record s { base = g }) eq
   (Lower.step-preserves (G.abortOwner w err) (W.base s) actual valid)
 enact-preserves (W.timeWaitDelivery w err) s eq valid with O.advance
   (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = control-preserves Close.acknowledgeDelivery
   (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq
   (source-valid c s (O.next {a = O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))} actual O.done) valid)
 enact-preserves (W.releaseDelivery caller worker err) s eq valid with G.step (G.abortOwner worker err) (W.base s) in aborted
 ... | nothing = case eq of λ ()
 ... | just g with O.advance (O.release caller (OutboundRelease.cancellationDelivered worker)) (W.source (record s { base = g })) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just c = case just-injective eq of λ { refl → source-valid c (record s { base = g })
   (O.next {a = O.release caller (OutboundRelease.cancellationDelivered worker)} acknowledged O.done)
   (Lower.step-preserves (G.abortOwner worker err) (W.base s) aborted valid) }
 enact-preserves (W.releaseTimeWaitDelivery caller worker err) s eq valid with O.advance
   (O.inbound (Machine.cleanupStep worker (Cleanup.interruptTimeWait err))) (W.source s) in interrupted
 ... | nothing = case eq of λ ()
 ... | just c with O.advance (O.release caller (OutboundRelease.cancellationDelivered worker)) c in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just c′ = case just-injective eq of λ { refl → source-valid c′ s
   (O.next {a = O.inbound (Machine.cleanupStep worker (Cleanup.interruptTimeWait err))} interrupted
     (O.next {a = O.release caller (OutboundRelease.cancellationDelivered worker)} acknowledged O.done)) valid }
 step-preserves : ∀ a s {t} → W.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with W.choose a s
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid
 local-valid : ∀ fs s → Valid s → Valid (record s { exits = fs })
 local-valid fs s valid = valid

import ConnectionManagement.MuxExitCancellation as CancellationModel
module Cancellation (isBearerClosed : ErrorId → Bool)
 (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains isBearerClosed s t → Obs s → Obs t) where
 private module X = CancellationModel isBearerClosed using (State; deliver; deliverShutdown; observeCancellation; observeErrorTraceException; run; shutdownDelivery; step; target; traceThrew)
 private module W = ExitModel isBearerClosed using (handshakeDelivery; handshakeAction; deliverShutdownHandshake; bodyExited; bufferScope; classifying; cleanupComplete; edit; errorTracing; exits; finalizing; nodeDelivery; nodeRethrow; peerRethrow; phase; resultAvailable; shutdown; syncException)
 private module Lower = Exit isBearerClosed Obs stable using (Valid; control-preserves; local-valid; step-preserves)
 Valid : X.State → Set
 Valid = Lower.Valid
 deliver-preserves : ∀ window w err s {t} → X.deliver window w err s ≡ just t → Valid s → Valid t
 deliver-preserves window w err s eq valid with lookup w (W.exits s) in found
 ... | nothing = case eq of λ ()
 ... | just f with X.target window err (W.phase f)
 ...   | nothing = case eq of λ ()
 ...   | just pc = case just-injective eq of λ { refl → Lower.local-valid (W.edit w f pc s) s  valid }
 trace-preserves : ∀ w err s {t} → X.traceThrew w err s ≡ just t → Valid s → Valid t
 trace-preserves w err s eq valid with lookup w (W.exits s) in found
 ... | nothing = case eq of λ ()
 ... | just f with W.phase f
 ...   | W.errorTracing original policy = case just-injective eq of λ { refl → Lower.local-valid (W.edit w f (W.bodyExited (W.syncException err)) s) s  valid }
 ...   | W.bufferScope outcome = case eq of λ ()
 ...   | W.classifying original = case eq of λ ()
 ...   | W.peerRethrow original = case eq of λ ()
 ...   | W.nodeDelivery original = case eq of λ ()
 ...   | W.nodeRethrow original = case eq of λ ()
 ...   | W.bodyExited result = case eq of λ ()
 ...   | W.finalizing result = case eq of λ ()
 ...   | W.cleanupComplete result outcome = case eq of λ ()
 ...   | W.resultAvailable result outcome = case eq of λ ()
 shutdown-preserves : ∀ window err s {t} → X.shutdownDelivery window err s ≡ just t → Valid s → Valid t
 shutdown-preserves window err s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with X.deliver window w err s in delivered
 ...   | nothing = case eq of λ ()
 ...   | just next = Lower.control-preserves Close.acknowledgeDelivery next eq (deliver-preserves window w err s delivered valid)
 shutdown-preserves window err s eq valid | Close.initial = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.reading = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.sendReady e w = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.awaitResults = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.closed = case eq of λ ()
 step-preserves : ∀ a s {t} → X.step a s ≡ just t → Valid s → Valid t
 step-preserves (X.run a) = Lower.step-preserves a
 step-preserves (X.observeCancellation window w err) = deliver-preserves window w err
 step-preserves (X.deliverShutdown window err) = shutdown-preserves window err
 step-preserves (X.observeErrorTraceException w err) = trace-preserves w err

