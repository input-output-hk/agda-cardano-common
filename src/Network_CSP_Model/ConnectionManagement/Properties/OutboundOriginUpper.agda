{-# OPTIONS --guardedness #-}

-- Lift exact active-acquisition effects through actual server wrappers.
module ConnectionManagement.Properties.OutboundOriginUpper where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId; HandleId)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
open import ConnectionManagement.IGTypes using (clean; errored; number)
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxDeltaQ as DeltaQModel
import ConnectionManagement.MuxCatchUnwind as CatchModel
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.ServerAdmission as AdmissionModel
import ConnectionManagement.ServerIGExit as IGExitModel
open import ConnectionManagement.Properties.OutboundOriginEffect using (Effect; same)
import ConnectionManagement.Properties.OutboundOriginLower as Lower

module DeltaQ (b : ErrorId → Bool) where
 private module D = DeltaQModel b using (source; allowed; applyFault; base; begin; beginDeltaQ; beginInitiator; beginInitiatorTrace; captured; complete; deliverInitiatorShutdown; deliverShutdown; delivery; entryPhase; faultPlan; finishAction; initiatorFaultPlan; initiatorReady; invoked; muxInvoked; muxReturned; observeException; observeInitiatorException; observeInitiatorReturn; observeReturn; payload; phase; ready; returnInitiator; returned; run; step; throw; throwInitiator; throwing; tickets; wrapMonitor)
 private module M = MonitorModel b using (finishProtocolTrace)
 private module R = UnwindModel b using (async; base; enact; step)
 private module W = ExitModel b using (shutdown)
 private module Raw = Lower.Unwind b using (effect; enact-effect)

 apply-effect : ∀ w p ack s {t} → D.applyFault w p ack s ≡ just t → Effect (D.source s) (D.source t)
 apply-effect w p ack s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just savedTicket with R.enact (D.delivery ack p) (D.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just r = case just-injective eq of λ { refl → Raw.enact-effect (D.delivery ack p) (D.base s) actual }
 throw-effect : ∀ w result ack s {t} → D.throw w result ack s ≡ just t → Effect (D.source s) (D.source t)
 throw-effect w result ack s eq with D.faultPlan w result s
 ... | nothing = case eq of λ ()
 ... | just p = apply-effect w p ack s eq
 throw-initiator-effect : ∀ w result ack s {t} → D.throwInitiator w result ack s ≡ just t → Effect (D.source s) (D.source t)
 throw-initiator-effect w result ack s eq with D.initiatorFaultPlan w result s
 ... | nothing = case eq of λ ()
 ... | just p = apply-effect w p ack s eq

 begin-preserves : ∀ w s {t} → D.begin w s ≡ just t → Effect (D.source s) (D.source t)
 begin-preserves w s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with D.entryPhase observedTicket ∧ D.ready w observedTicket s
 ...   | false = case eq of λ ()
 ...   | true = case just-injective eq of λ { refl → same refl }
 complete-preserves : ∀ w s {t} → D.complete w s ≡ just t → Effect (D.source s) (D.source t)
 complete-preserves w s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with D.phase observedTicket | D.ready w observedTicket s
 ...   | D.invoked | true with R.step (D.finishAction w (D.payload observedTicket)) (D.base s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just r = case just-injective eq of λ { refl → Raw.effect (D.finishAction w (D.payload observedTicket)) (D.base s) actual }
 complete-preserves w s eq | just observedTicket | D.captured | _ = case eq of λ ()
 complete-preserves w s eq | just observedTicket | D.muxInvoked | _ = case eq of λ ()
 complete-preserves w s eq | just observedTicket | D.muxReturned | _ = case eq of λ ()
 complete-preserves w s eq | just observedTicket | D.returned | _ = case eq of λ ()
 complete-preserves w s eq | just observedTicket | D.throwing | _ = case eq of λ ()
 complete-preserves w s eq | just observedTicket | D.invoked | false = case eq of λ ()
 begin-initiator-preserves : ∀ w s {t} → D.beginInitiator w s ≡ just t → Effect (D.source s) (D.source t)
 begin-initiator-preserves w s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with D.phase observedTicket | D.initiatorReady w observedTicket s
 ...   | D.captured | true = case just-injective eq of λ { refl → same refl }
 ...   | D.captured | false = case eq of λ ()
 ...   | D.muxInvoked | _ = case eq of λ ()
 ...   | D.muxReturned | _ = case eq of λ ()
 ...   | D.invoked | _ = case eq of λ ()
 ...   | D.returned | _ = case eq of λ ()
 ...   | D.throwing | _ = case eq of λ ()
 return-initiator-preserves : ∀ w s {t} → D.returnInitiator w s ≡ just t → Effect (D.source s) (D.source t)
 return-initiator-preserves w s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with D.phase observedTicket | D.initiatorReady w observedTicket s
 ...   | D.muxInvoked | true with D.payload observedTicket
 ...     | Types.protocolCompletion Mux.initiatorJob n gen clean = case just-injective eq of λ { refl → same refl }
 ...     | Types.protocolCompletion Mux.initiatorJob n gen (errored err) with R.step (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) in actual
 ...       | nothing = case eq of λ ()
 ...       | just r = case just-injective eq of λ { refl → Raw.effect (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) actual }
 return-initiator-preserves w s eq | just observedTicket | D.muxInvoked | true | Types.protocolCompletion Mux.responderJob n gen result = case eq of λ ()
 return-initiator-preserves w s eq | just observedTicket | D.muxInvoked | true | Types.infraMuxer err = case eq of λ ()
 return-initiator-preserves w s eq | just observedTicket | D.muxInvoked | true | Types.infraDemuxer err = case eq of λ ()
 return-initiator-preserves w s eq | just observedTicket | D.muxInvoked | false = case eq of λ ()
 return-initiator-preserves w s eq | just observedTicket | D.captured | _ = case eq of λ ()
 return-initiator-preserves w s eq | just observedTicket | D.muxReturned | _ = case eq of λ ()
 return-initiator-preserves w s eq | just observedTicket | D.invoked | _ = case eq of λ ()
 return-initiator-preserves w s eq | just observedTicket | D.returned | _ = case eq of λ ()
 return-initiator-preserves w s eq | just observedTicket | D.throwing | _ = case eq of λ ()

 effect : ∀ a s {t} → D.step a s ≡ just t → Effect (D.source s) (D.source t)
 effect (D.run a) s eq with D.allowed a s
 ... | false = case eq of λ ()
 ... | true with R.step a (D.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just r = case just-injective eq of λ { refl → Raw.effect a (D.base s) actual }
 effect (D.beginDeltaQ w) = begin-preserves w
 effect (D.observeReturn w) = complete-preserves w
 effect (D.observeException w result) s eq = throw-effect w result false s eq
 effect (D.beginInitiatorTrace w) = begin-initiator-preserves w
 effect (D.observeInitiatorReturn w) = return-initiator-preserves w
 effect (D.observeInitiatorException w result) s eq = throw-initiator-effect w result false s eq
 effect (D.deliverShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
 ... | Close.awaitDelivery e w = throw-effect w (R.async err) true s eq
 effect (D.deliverShutdown err) s eq | Close.initial = case eq of λ ()
 effect (D.deliverShutdown err) s eq | Close.reading = case eq of λ ()
 effect (D.deliverShutdown err) s eq | Close.sendReady e w = case eq of λ ()
 effect (D.deliverShutdown err) s eq | Close.awaitResults = case eq of λ ()
 effect (D.deliverShutdown err) s eq | Close.closed = case eq of λ ()
 effect (D.deliverInitiatorShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
 ... | Close.awaitDelivery e w = throw-initiator-effect w (R.async err) true s eq
 effect (D.deliverInitiatorShutdown err) s eq | Close.initial = case eq of λ ()
 effect (D.deliverInitiatorShutdown err) s eq | Close.reading = case eq of λ ()
 effect (D.deliverInitiatorShutdown err) s eq | Close.sendReady e w = case eq of λ ()
 effect (D.deliverInitiatorShutdown err) s eq | Close.awaitResults = case eq of λ ()
 effect (D.deliverInitiatorShutdown err) s eq | Close.closed = case eq of λ ()

module Catch (b : ErrorId → Bool) where
 private module C = CatchModel b using (source; action; allowed; apply; base; cancellation; deliverShutdown; observe; observeCancellation; observeException; run; select; step; synchronous)
 private module D = DeltaQModel b using (base; delivery; step)
 private module R = UnwindModel b using (base; enact)
 private module W = ExitModel b using (shutdown)
 private module Raw = Lower.Unwind b using (enact-effect)
 private module Below = DeltaQ b using (effect)

 apply-effect : ∀ w p ack s {t} → C.apply w p ack s ≡ just t → Effect (C.source s) (C.source t)
 apply-effect w p ack s eq with R.enact (D.delivery ack (C.action p)) (D.base (C.base s)) in actual
 ... | nothing = case eq of λ ()
 ... | just r = case just-injective eq of λ { refl → Raw.enact-effect (D.delivery ack (C.action p)) (D.base (C.base s)) actual }
 observe-effect : ∀ w reason ack s {t} → C.observe w reason ack s ≡ just t → Effect (C.source s) (C.source t)
 observe-effect w reason ack s eq with C.select w reason s
 ... | nothing = case eq of λ ()
 ... | just p = apply-effect w p ack s eq
 effect : ∀ a s {t} → C.step a s ≡ just t → Effect (C.source s) (C.source t)
 effect (C.run a) s eq with C.allowed a
 ... | false = case eq of λ ()
 ... | true with D.step a (C.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → Below.effect a (C.base s) actual }

 effect (C.observeException w err) s eq = observe-effect w (C.synchronous err) false s eq
 effect (C.observeCancellation w site err) s eq = observe-effect w (C.cancellation site err) false s eq

 effect (C.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base (D.base (C.base s))))
 ... | Close.awaitDelivery e w = observe-effect w (C.cancellation site err) true s eq
 effect (C.deliverShutdown site err) s eq | Close.initial = case eq of λ ()
 effect (C.deliverShutdown site err) s eq | Close.reading = case eq of λ ()
 effect (C.deliverShutdown site err) s eq | Close.sendReady e w = case eq of λ ()
 effect (C.deliverShutdown site err) s eq | Close.awaitResults = case eq of λ ()
 effect (C.deliverShutdown site err) s eq | Close.closed = case eq of λ ()

module Publication (b : ErrorId → Bool) where
 private module N = PublicationModel b using (source; action; allowed; apply; base; deliverShutdown; observe; observeFailure; raw; run; select; step)
 private module C = CatchModel b using (step)
 private module D = DeltaQModel b using (delivery)
 private module R = UnwindModel b using (async; base; enact)
 private module W = ExitModel b using (shutdown)
 private module Raw = Lower.Unwind b using (enact-effect)
 private module Below = Catch b using (effect)

 apply-effect : ∀ w p ack s {t} → N.apply w p ack s ≡ just t → Effect (N.source s) (N.source t)
 apply-effect w p ack s eq with R.enact (D.delivery ack (N.action p)) (N.raw s) in actual
 ... | nothing = case eq of λ ()
 ... | just r = case just-injective eq of λ { refl → Raw.enact-effect (D.delivery ack (N.action p)) (N.raw s) actual }
 observe-effect : ∀ w site result ack s {t} → N.observe w site result ack s ≡ just t → Effect (N.source s) (N.source t)
 observe-effect w site result ack s eq with N.select w site result s
 ... | nothing = case eq of λ ()
 ... | just p = apply-effect w p ack s eq
 effect : ∀ a s {t} → N.step a s ≡ just t → Effect (N.source s) (N.source t)
 effect (N.run a) s eq with N.allowed a s
 ... | false = case eq of λ ()
 ... | true with C.step a (N.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → Below.effect a (N.base s) actual }

 effect (N.observeFailure w site result) s eq = observe-effect w site result false s eq

 effect (N.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base (N.raw s)))
 ... | Close.awaitDelivery e w = observe-effect w site (R.async err) true s eq
 effect (N.deliverShutdown site err) s eq | Close.initial = case eq of λ ()
 effect (N.deliverShutdown site err) s eq | Close.reading = case eq of λ ()
 effect (N.deliverShutdown site err) s eq | Close.sendReady e w = case eq of λ ()
 effect (N.deliverShutdown site err) s eq | Close.awaitResults = case eq of λ ()
 effect (N.deliverShutdown site err) s eq | Close.closed = case eq of λ ()

module Server (isBearerClosed : ErrorId → Bool) where
 private module SA = AdmissionModel isBearerClosed using (source; acceptedFork; accepting; allowed; base; bodyExited; calling; chooseScope; closeDisconnected; closeException; closePrefix; closePrefixWorker; closeWorker; enactClose; enactPrefixClose; enactScope; forkAccepted; fresh; inherit; listenerOpen; nextException; nextNormal; observeException; observeReturn; pc; physicalAction; prefixCloseFailed; prefixException; prefixMatches; prefixReturned; publishWorkerResult; resultAvailable; run; runMachine; sameLimit; scope; scopeAdvance; shared; stage; step; workerClose; workerException; workerPrefixException; workerPrefixReturned; workerResult; workerReturned; workers)
 private module N = PublicationModel isBearerClosed using (step)
 private module PublishFacts = Publication isBearerClosed using (effect)
 -- Successful birth writes an admission and socket; physical metadata is separate.
 fork-preserves : ∀ w req s {t} → SA.forkAccepted w req s ≡ just t → Effect (SA.source s) (SA.source t)
 fork-preserves w req s eq with SA.accepting (SA.stage s) | SA.listenerOpen s |
   SA.sameLimit req (SA.workers s) | SA.fresh w s | SA.fresh (Shared.child req) s |
   w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (SA.shared s))
 ... | true | true | true | true | true | no _ | nothing =
   case just-injective eq of λ { refl → same refl }
 ... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
 ... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
 ... | true | true | false | _ | _ | _ | _ = case eq of λ ()
 ... | true | true | true | false | _ | _ | _ = case eq of λ ()
 ... | true | true | true | true | false | _ | _ = case eq of λ ()
 ... | true | true | true | true | true | yes _ | _ = case eq of λ ()
 ... | true | true | true | true | true | no _ | just _ = case eq of λ ()

 -- Return, exception and result observations change only raw-worker metadata.
 return-preserves : ∀ w s {t} → SA.observeReturn w s ≡ just t → Effect (SA.source s) (SA.source t)
 return-preserves w s eq with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.completedHandshake (Shared.connected _) = case just-injective eq of λ { refl → same refl }
 ...   | SA.calling | Shared.completedHandshake (Shared.disconnected _) = case just-injective eq of λ { refl → same refl }
 ...   | SA.calling | Shared.acquireMap = case eq of λ ()
 ...   | SA.calling | Shared.count _ = case eq of λ ()
 ...   | SA.calling | Shared.prepare _ = case eq of λ ()
 ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
 ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket _ = case eq of λ ()
 ...   | SA.calling | Shared.finished _ = case eq of λ ()
 ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
 ...   | SA.calling | Shared.awaitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
 ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
 ...   | SA.closeDisconnected | _ = case eq of λ ()
 ...   | SA.closeException _ | _ = case eq of λ ()
 ...   | SA.closePrefix _ _ | _ = case eq of λ ()
 ...   | SA.bodyExited _ | _ = case eq of λ ()
 ...   | SA.resultAvailable _ | _ = case eq of λ ()
 return-preserves w s eq | nothing | _ = case eq of λ ()
 return-preserves w s eq | just _ | nothing = case eq of λ ()
 prefix-return-preserves : ∀ w s {t} → SA.prefixReturned w s ≡ just t → Effect (SA.source s) (SA.source t)
 prefix-return-preserves w s eq with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.closeSocket Shared.hardLimitReached = case just-injective eq of λ { refl → same refl }
 ...   | SA.calling | Shared.acquireMap = case eq of λ ()
 ...   | SA.calling | Shared.count _ = case eq of λ ()
 ...   | SA.calling | Shared.prepare _ = case eq of λ ()
 ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
 ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
 ...   | SA.calling | Shared.finished _ = case eq of λ ()
 ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
 ...   | SA.calling | Shared.awaitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
 ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.completedHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket Shared.forbidden = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket Shared.forkFailed = case eq of λ ()
 ...   | SA.closeDisconnected | _ = case eq of λ ()
 ...   | SA.closeException _ | _ = case eq of λ ()
 ...   | SA.closePrefix _ _ | _ = case eq of λ ()
 ...   | SA.bodyExited _ | _ = case eq of λ ()
 ...   | SA.resultAvailable _ | _ = case eq of λ ()
 prefix-return-preserves w s eq | nothing | _ = case eq of λ ()
 prefix-return-preserves w s eq | just _ | nothing = case eq of λ ()
 prefix-exception-preserves : ∀ w err s {t} → SA.prefixException w err s ≡ just t → Effect (SA.source s) (SA.source t)
 prefix-exception-preserves w err s eq with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.closeSocket Shared.forbidden = case just-injective eq of λ { refl → same refl }
 ...   | SA.calling | Shared.closeSocket Shared.forkFailed = case just-injective eq of λ { refl → same refl }
 ...   | SA.calling | Shared.acquireMap = case eq of λ ()
 ...   | SA.calling | Shared.count _ = case eq of λ ()
 ...   | SA.calling | Shared.prepare _ = case eq of λ ()
 ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
 ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
 ...   | SA.calling | Shared.finished _ = case eq of λ ()
 ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
 ...   | SA.calling | Shared.awaitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
 ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.completedHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket Shared.hardLimitReached = case eq of λ ()
 ...   | SA.closeDisconnected | _ = case eq of λ ()
 ...   | SA.closeException _ | _ = case eq of λ ()
 ...   | SA.closePrefix _ _ | _ = case eq of λ ()
 ...   | SA.bodyExited _ | _ = case eq of λ ()
 ...   | SA.resultAvailable _ | _ = case eq of λ ()
 prefix-exception-preserves w err s eq | nothing | _ = case eq of λ ()
 prefix-exception-preserves w err s eq | just _ | nothing = case eq of λ ()
 exception-preserves : ∀ w err s {t} → SA.observeException w err s ≡ just t → Effect (SA.source s) (SA.source t)
 exception-preserves w err s eq with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → same refl }
 ...   | SA.calling | Shared.acquireMap = case eq of λ ()
 ...   | SA.calling | Shared.count _ = case eq of λ ()
 ...   | SA.calling | Shared.prepare _ = case eq of λ ()
 ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
 ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket _ = case eq of λ ()
 ...   | SA.calling | Shared.finished _ = case eq of λ ()
 ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
 ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
 ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.completedHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
 ...   | SA.closeDisconnected | _ = case eq of λ ()
 ...   | SA.closeException _ | _ = case eq of λ ()
 ...   | SA.closePrefix _ _ | _ = case eq of λ ()
 ...   | SA.bodyExited _ | _ = case eq of λ ()
 ...   | SA.resultAvailable _ | _ = case eq of λ ()
 exception-preserves w err s eq | nothing | _ = case eq of λ ()
 exception-preserves w err s eq | just _ | nothing = case eq of λ ()
 result-preserves : ∀ w s {t} → SA.publishWorkerResult w s ≡ just t → Effect (SA.source s) (SA.source t)
 result-preserves w s eq with lookup w (SA.workers s)
 ... | nothing = case eq of λ ()
 ... | just worker with SA.pc worker
 ...   | SA.bodyExited r = case just-injective eq of λ { refl → same refl }
 ...   | SA.calling = case eq of λ ()
 ...   | SA.closeDisconnected = case eq of λ ()
 ...   | SA.closeException _ = case eq of λ ()
 ...   | SA.closePrefix _ _ = case eq of λ ()
 ...   | SA.resultAvailable _ = case eq of λ ()

 -- Both successful/uncertain socket observations leave admission rows unchanged.
 enact-close-preserves : ∀ w worker outcome next s →
   Effect (SA.source s) (SA.source (SA.enactClose w worker outcome next s))
 enact-close-preserves w worker outcome next s = same refl
 enact-prefix-preserves : ∀ w worker result outcome s {t} → SA.enactPrefixClose w worker result outcome s ≡ just t →
   Effect (SA.source s) (SA.source t)
 enact-prefix-preserves w worker result nothing s eq with N.step
   (SA.runMachine (Machine.admissionStep w Admission.close)) (SA.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just n = case just-injective eq of λ { refl → PublishFacts.effect (SA.runMachine (Machine.admissionStep w Admission.close)) (SA.base s) advanced }
 enact-prefix-preserves w worker result (just err) s eq = case just-injective eq of λ
   { refl → enact-close-preserves w worker (just err) (SA.prefixCloseFailed result err) s }
 close-prefix-preserves : ∀ w worker failure result outcome s {t} →
   SA.closePrefixWorker w worker failure result outcome s ≡ just t → Effect (SA.source s) (SA.source t)
 close-prefix-preserves w worker failure result outcome s eq with SA.prefixMatches w failure s
 ... | false = case eq of λ ()
 ... | true = enact-prefix-preserves w worker result outcome s eq
 close-preserves : ∀ w outcome s {t} → SA.closeWorker w outcome s ≡ just t → Effect (SA.source s) (SA.source t)
 close-preserves w outcome s eq with lookup w (SA.workers s)
 ... | nothing = case eq of λ ()
 ... | just worker with SA.pc worker
 ...   | SA.closeDisconnected = case just-injective eq of λ
   { refl → enact-close-preserves w worker outcome (SA.nextNormal outcome) s }
 ...   | SA.closeException err = case just-injective eq of λ
   { refl → enact-close-preserves w worker outcome (SA.nextException err outcome) s }
 ...   | SA.closePrefix f r = close-prefix-preserves w worker f r outcome s eq
 ...   | SA.calling = case eq of λ ()
 ...   | SA.bodyExited _ = case eq of λ ()
 ...   | SA.resultAvailable _ = case eq of λ ()
 inherit-preserves : ∀ a s {t} → SA.inherit a s ≡ just t → Effect (SA.source s) (SA.source t)
 inherit-preserves a s eq with SA.allowed a s
 ... | false = case eq of λ ()
 ... | true with N.step a (SA.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just n = case just-injective eq of λ { refl → PublishFacts.effect a (SA.base s) actual }
 scope-enact-preserves : ∀ p s {t} → SA.enactScope p s ≡ just t → Effect (SA.source s) (SA.source t)
 scope-enact-preserves p s eq with SA.physicalAction p
 ... | nothing = case just-injective eq of λ { refl → same refl }
 ... | just command with N.step command (SA.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just n = case just-injective eq of λ { refl → PublishFacts.effect command (SA.base s) actual }
 scope-preserves : ∀ a s {t} → SA.scopeAdvance a s ≡ just t → Effect (SA.source s) (SA.source t)
 scope-preserves a s eq with SA.chooseScope a s
 ... | nothing = case eq of λ ()
 ... | just p = scope-enact-preserves p s eq
 effect : ∀ a s {t} → SA.step a s ≡ just t → Effect (SA.source s) (SA.source t)
 effect (SA.acceptedFork w req) = fork-preserves w req
 effect (SA.run a) = inherit-preserves a
 effect (SA.workerReturned w) = return-preserves w
 effect (SA.workerPrefixReturned w) = prefix-return-preserves w
 effect (SA.workerPrefixException w err) = prefix-exception-preserves w err
 effect (SA.workerException w err) = exception-preserves w err
 effect (SA.workerClose w outcome) = close-preserves w outcome
 effect (SA.workerResult w) = result-preserves w
 effect (SA.scope a) = scope-preserves a

module IGExit (b : ErrorId → Bool) where
 private module E = IGExitModel b using (source; abandon; ownFailure; base; choose; delegate; enact; finish; local; step)
 private module SA = AdmissionModel b using (step)
 private module ServerFacts = Server b using (effect)
 enact-preserves : ∀ p s {t} → E.enact p s ≡ just t → Effect (E.source s) (E.source t)
 enact-preserves (E.delegate a e) s eq with SA.step a (E.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just server = case just-injective eq of λ { refl → ServerFacts.effect a (E.base s) actual }
 enact-preserves (E.local e) s eq = case just-injective eq of λ { refl → same refl }
 enact-preserves (E.abandon r) s eq = case just-injective eq of λ { refl → same refl }
 enact-preserves (E.ownFailure r f) s eq = case just-injective eq of λ { refl → same refl }
 enact-preserves (E.finish e) s eq = case just-injective eq of λ { refl → same refl }
 effect : ∀ a s {t} → E.step a s ≡ just t → Effect (E.source s) (E.source t)
 effect a s eq with E.choose a s
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq
