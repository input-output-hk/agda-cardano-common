{-# OPTIONS --guardedness #-}

-- Caller bookkeeping at the shared Server/peer frontend. A Server step keeps
-- every outbound caller key and result table: a key-changing outbound action
-- has a caller, which serverAllowed refuses. A core step is exactly its own
-- outbound-machine step up to key-preserving writes.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysShared (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.MuxCatchUnwind as Catch
import ConnectionManagement.MuxDeltaQ as Delta
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.MuxHandlerExit as HandlerExit
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxResultMonitor as Monitor
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxHandlerSupervision as Handler
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.PeerContext as Context
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysIGExit as IGExitKeys
private
  module K = Combined isBearerClosed isIOManagerError
  module E = Exit isBearerClosed
  module S = Server isBearerClosed
  module N = Publication isBearerClosed
  module C = Catch isBearerClosed
  module D = Delta isBearerClosed
  module R′ = Unwind isBearerClosed
  module X = Cancellation isBearerClosed
  module W = HandlerExit isBearerClosed
  module G = Group isBearerClosed
  module M = Monitor isBearerClosed
  module U = Handler Types.TypedResult
  module Keys = IGExitKeys isBearerClosed

-- A Server-layer root is exactly a nested key-changing outbound action.
key-just : ∀ y {x} → keyRoot y ≡ just x → y ≡ x × keyChanging x ≡ true
key-just y eq with keyChanging y in kc
... | true = case just-injective eq of λ { refl → refl , kc }
... | false = case eq of λ ()
outbound-root : ∀ a {x} → Keys.rootE a ≡ just x → a ≡ E.run (S.run (S.runOutbound x)) × keyChanging x ≡ true
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.run (U.run (B.outbound y))))))))))))) eq with key-just y eq
... | refl , kc = refl , kc
outbound-root (E.receive _ _) ()
outbound-root E.captureSnapshot ()
outbound-root E.invokeFinal ()
outbound-root E.returnFinal ()
outbound-root E.finishFinal ()
outbound-root (E.failFinal _) ()
outbound-root (E.fail _ _) ()
outbound-root (E.run (S.acceptedFork _ _)) ()
outbound-root (E.run (S.workerReturned _)) ()
outbound-root (E.run (S.workerPrefixReturned _)) ()
outbound-root (E.run (S.workerPrefixException _ _)) ()
outbound-root (E.run (S.workerException _ _)) ()
outbound-root (E.run (S.workerClose _ _)) ()
outbound-root (E.run (S.workerResult _)) ()
outbound-root (E.run (S.scope _)) ()
outbound-root (E.run (S.run (N.observeFailure _ _ _))) ()
outbound-root (E.run (S.run (N.deliverShutdown _ _))) ()
outbound-root (E.run (S.run (N.run (C.observeException _ _)))) ()
outbound-root (E.run (S.run (N.run (C.observeCancellation _ _ _)))) ()
outbound-root (E.run (S.run (N.run (C.deliverShutdown _ _)))) ()
outbound-root (E.run (S.run (N.run (C.run (D.beginDeltaQ _))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.observeReturn _))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.beginInitiatorTrace _))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.observeInitiatorReturn _))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.observeException _ _))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.observeInitiatorException _ _))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.deliverShutdown _))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.deliverInitiatorShutdown _))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.observeFailure _ _ _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.observeCancellation _ _ _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.deliverShutdown _ _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.beginClose _ _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.requestCancel _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.deliverCancel _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.join _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.finishClose _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.continueSync _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.writeAsyncFailure _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.beginDead _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.sampleDead _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.commitDead _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.finishDead _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.handoff _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.observeDeadTraceException _ _)))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.observeCancellation _ _ _))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.deliverShutdown _ _))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.observeErrorTraceException _ _))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.beginExit _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.observeBufferReturn _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.observeBufferException _ _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.choosePolicy _ _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.observeErrorTrace _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.observeNodeDelivery _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.rethrow _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.enterFinalizer _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.finishCleanup _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.publishAsyncResult _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.cleanup _ _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.shutdownStep _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.deliverShutdownMux _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.deliverShutdownTimeWait _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.acknowledgeFinished)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.deliverReleaseMux _ _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.deliverReleaseTimeWait _ _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.acknowledgeReleaseFinished _)))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.requestShutdown _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.selectShutdown _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.observeStoppingTrace _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.writeStopping _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.requestGroupCancel _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.deliverGroup _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.joinGroup _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.finishGroup _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.drainEmpty _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.timeout2Elapsed _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.writeStopped _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.observeTraceStopped _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.sampleStoppedTracer _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.commitStoppedTracer _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.finishStoppedTrace _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.retireCounters _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.captureGroup _ _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.finishChildUnwind _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.unwindReplacedBySync _ _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.abortOwner _ _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.beginWholeClose _ _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.requestWholeCancel _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.deliverWhole _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.joinWhole _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.finishWholeClose _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.finishNormalScope _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.writeAsyncFailure _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.beginAsyncDead _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.sampleAsyncTracer _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.commitAsyncTracer _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.finishAsyncDead _))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.consume _)))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.handleSelected _)))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.sampleTracer _)))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.commitTracer _)))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.finishProtocolTrace _)))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.beginDead _)))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.finishDead _)))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.forkResponder _ _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.forkInitiator _ _ _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.enterProtocolBody _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.appendProtocolPayload _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.egressMuxer _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.registerProtocol _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.protocolReturned _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.commitClean _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.returnProtocol _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.publishProtocol _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.deregisterProtocol _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.asyncProtocolResult _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.protocolException _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.infrastructureReturn _ _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.publishInfra _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.deregisterInfra _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.asyncInfraResult _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.control _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.submitDbWrite _ _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.awaitDbWrite _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.dbWriteFailed _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.writerComplete _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.writerSeal _))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.run (U.negotiate _ _ _)))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.run (U.allocateHandle _ _ _)))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.run (U.configureMux _ _ _ _ _)))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.run (U.registerCounters _)))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.run (U.egressSetup _)))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.run (U.publishSuccess _)))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.run (U.startupStep _ _)))))))))))) ()
outbound-root (E.run (S.run (N.run (C.run (D.run (R′.run (X.run (W.run (G.run (M.run (P.run (U.run (B.handler _))))))))))))) ()


-- Every key-changing outbound action names its caller, so a raw Server step
-- with it is refused.
server-blocks : ∀ x s → keyChanging x ≡ true → K.serverAllowed (E.run (S.run (S.runOutbound x))) s ≡ false
server-blocks (O.beginAcquire w r) s kc = refl
server-blocks (O.beginRelease w k) s kc = refl
server-blocks (O.acquire w A.returnResult) s kc = refl
server-blocks (O.release w R.returnResult) s kc = refl
server-blocks (O.inbound _) s ()
server-blocks (O.acquire w (A.select e)) s ()
server-blocks (O.acquire w A.readCounters) s ()
server-blocks (O.acquire w A.newPromise) s ()
server-blocks (O.acquire w A.openOK) s ()
server-blocks (O.acquire w A.configureOK) s ()
server-blocks (O.acquire w A.bindOK) s ()
server-blocks (O.acquire w A.connectOK) s ()
server-blocks (O.acquire w (A.gotLocal p)) s ()
server-blocks (O.acquire w A.updateLocalAddress) s ()
server-blocks (O.acquire w A.forkOK) s ()
server-blocks (O.acquire w A.commitConnected) s ()
server-blocks (O.acquire w A.readResult) s ()
server-blocks (O.acquire w A.commitHandshake) s ()
server-blocks (O.acquire w (A.failIO e)) s ()
server-blocks (O.acquire w (A.closeFailed e)) s ()
server-blocks (O.acquire w A.closeOK) s ()
server-blocks (O.acquire w A.removeReservation) s ()
server-blocks (O.acquire w A.waitNegotiated) s ()
server-blocks (O.release w R.transactionStep) s ()
server-blocks (O.release w R.checkAssertion) s ()
server-blocks (O.release w R.readCounters) s ()
server-blocks (O.release w R.registerTimer) s ()
server-blocks (O.release w R.expireTimer) s ()
server-blocks (O.release w R.selectWakeup) s ()
server-blocks (O.release w R.commitTimeout) s ()
server-blocks (O.release w R.requestCancellation) s ()
server-blocks (O.release w (R.transactionPruning ss)) s ()
server-blocks (O.release w (R.cancellationDelivered t)) s ()

-- Server steps keep the peer context and the caller bookkeeping.
server-keys : ∀ a s {t} → K.step (K.serverStep a) s ≡ just t → KeySame (K.source s) (K.source t) × K.context t ≡ K.context s
server-keys a s eq with K.serverAllowed a s in allowed
... | false = case eq of λ ()
... | true with E.step a (K.server s) in stepped
...   | nothing = case eq of λ ()
...   | just e with Keys.rootE a in rooted
...     | nothing = case just-injective eq of λ { refl → subst (λ r → Effect r (E.source (K.server s)) (E.source e)) rooted
  (Keys.step-keysE a (K.server s) stepped) , refl }
...     | just x with outbound-root a rooted
...       | refl , kc = case trans (sym allowed) (server-blocks x s kc) of λ ()

-- A core step's root is its own outbound action.
core-root : ∀ a → Keys.rootE (K.coreAction a) ≡ keyRoot a
core-root (O.inbound x) = refl
core-root (O.beginAcquire w r) = refl
core-root (O.acquire w a) = refl
core-root (O.beginRelease w k) = refl
core-root (O.release w a) = refl
core-keys : ∀ a s {t} → K.step (K.coreStep a) s ≡ just t →
  Effect (keyRoot a) (K.source s) (K.source t) × K.context t ≡ K.noteCore a (K.source t) (K.context s)
core-keys a s eq with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s) in stepped
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → subst (λ r → Effect r (E.source (K.server s)) (E.source e)) (core-root a)
  (Keys.step-keysE (K.coreAction a) (K.server s) stepped) , refl }
