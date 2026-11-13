{-# OPTIONS --guardedness #-}

-- Joint core/PC content through the higher Server writers, carrying any
-- certified observer of retained physical references.
module ConnectionManagement.Properties.LiveTrackerAuxLayers where

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
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
open import ConnectionManagement.IGTypes using (clean; errored; number)
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxDeltaQ as DeltaQModel
import ConnectionManagement.MuxCatchUnwind as CatchModel
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.ServerAdmission as AdmissionModel
import ConnectionManagement.ServerIGExit as IGExitModel
import ConnectionManagement.ServerPeers as SharedModel
import ConnectionManagement.PeerSupervision as PeerModel
import ConnectionManagement.PeerContext as PeerContext
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindFacts
import ConnectionManagement.Properties.MuxDeltaQ as DeltaFacts
import ConnectionManagement.Properties.MuxCatchUnwind as CatchFacts
import ConnectionManagement.Properties.CleanupPeers as CleanupPeers
import ConnectionManagement.Properties.InboundOriginRuntime as OriginRuntime
import ConnectionManagement.Properties.InboundOriginPeers as OriginPeers
open import ConnectionManagement.Properties.LiveTrackerAuxUnwind using (module Unwind; module Exit)
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport

import ConnectionManagement.Properties.LiveTrackerContentPeers as PeersContent
open import Data.List.Relation.Unary.All using ([]; _∷_)

-- DeltaQ callbacks run actual lower steps or select a startup fault.
module DeltaQ (b : ErrorId → Bool)
 (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains b s t → Obs s → Obs t) where
 private module D = DeltaQModel b using (State; allowed; applyFault; base; begin; beginDeltaQ; beginInitiator; beginInitiatorTrace; captured; complete; deliverInitiatorShutdown; deliverShutdown; delivery; entryPhase; faultPlan; finishAction; initial; initiatorFaultPlan; initiatorReady; invoked; muxInvoked; muxReturned; observeException; observeInitiatorException; observeInitiatorReturn; observeReturn; payload; phase; ready; returnInitiator; returned; run; step; throw; throwInitiator; throwing; tickets; wrapMonitor)
 private module M = MonitorModel b using (finishProtocolTrace)
 private module R = UnwindModel b using (Fault; async; base; enact; faults; initial; poolBody; setSource; step)
 private module W = ExitModel b using (shutdown)
 private module Raw = Unwind b Obs stable
 private module F = UnwindFacts b using (Selection; selection-observation)
 private module DF = DeltaFacts b using (fault-selection)
 Valid : D.State → Set
 Valid s = Raw.Valid (D.base s)
 selection-safe : ∀ {w result route s p} → F.Selection w result route s p → Raw.Valid s → Raw.PlanSafe p s
 selection-safe {w} {result} {route} {s} selected valid rewrite F.Selection.plan-shape selected = Raw.safe-local
 delivery-safe : ∀ ack p s → Raw.PlanSafe p s → Raw.PlanSafe (D.delivery ack p) s
 delivery-safe false p s safe = safe
 delivery-safe true p s safe = Raw.safe-acknowledge safe
 apply-preserves : ∀ w p ack s {t} → D.applyFault w p ack s ≡ just t → Valid s → Raw.PlanSafe p (D.base s) →
   Valid t
 apply-preserves w p ack s eq valid safe with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with R.enact (D.delivery ack p) (D.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just r = case just-injective eq of λ { refl → Raw.enact-preserves (D.delivery ack p) (D.base s) actual valid
   (delivery-safe ack p (D.base s) safe) }
 throw-preserves : ∀ w result ack s {t} → D.throw w result ack s ≡ just t → Valid s →
   Valid t
 throw-preserves w result ack s eq valid with D.faultPlan w result s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = apply-preserves w p ack s eq valid (selection-safe selected valid)
   where selected = DF.fault-selection w result s chosen
 initiator-selection : ∀ w result s {p} → D.initiatorFaultPlan w result s ≡ just p → F.Selection w result (λ _ _ → just R.poolBody) (D.base s) p
 initiator-selection w result s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with D.phase observedTicket | D.initiatorReady w observedTicket s
 ...   | D.muxInvoked | true = F.selection-observation w result (λ _ _ → just R.poolBody) (D.base s) eq
 ...   | D.muxInvoked | false = case eq of λ ()
 ...   | D.captured | _ = case eq of λ ()
 ...   | D.muxReturned | _ = case eq of λ ()
 ...   | D.invoked | _ = case eq of λ ()
 ...   | D.returned | _ = case eq of λ ()
 ...   | D.throwing | _ = case eq of λ ()
 throw-initiator-preserves : ∀ w result ack s {t} → D.throwInitiator w result ack s ≡ just t → Valid s →
   Valid t
 throw-initiator-preserves w result ack s eq valid with D.initiatorFaultPlan w result s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = apply-preserves w p ack s eq valid (selection-safe selected valid)
   where selected = initiator-selection w result s chosen
 begin-preserves : ∀ w s {t} → D.begin w s ≡ just t → Valid s → Valid t
 begin-preserves w s eq valid with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with D.entryPhase observedTicket ∧ D.ready w observedTicket s
 ...   | false = case eq of λ ()
 ...   | true = case just-injective eq of λ { refl → valid }
 complete-preserves : ∀ w s {t} → D.complete w s ≡ just t → Valid s → Valid t
 complete-preserves w s eq valid with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with D.phase observedTicket | D.ready w observedTicket s
 ...   | D.invoked | true with R.step (D.finishAction w (D.payload observedTicket)) (D.base s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just r = case just-injective eq of λ { refl → Raw.step-preserves (D.finishAction w (D.payload observedTicket)) (D.base s) actual valid }
 complete-preserves w s eq valid | just observedTicket | D.captured | _ = case eq of λ ()
 complete-preserves w s eq valid | just observedTicket | D.muxInvoked | _ = case eq of λ ()
 complete-preserves w s eq valid | just observedTicket | D.muxReturned | _ = case eq of λ ()
 complete-preserves w s eq valid | just observedTicket | D.returned | _ = case eq of λ ()
 complete-preserves w s eq valid | just observedTicket | D.throwing | _ = case eq of λ ()
 complete-preserves w s eq valid | just observedTicket | D.invoked | false = case eq of λ ()
 begin-initiator-preserves : ∀ w s {t} → D.beginInitiator w s ≡ just t → Valid s → Valid t
 begin-initiator-preserves w s eq valid with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with D.phase observedTicket | D.initiatorReady w observedTicket s
 ...   | D.captured | true = case just-injective eq of λ { refl → valid }
 ...   | D.captured | false = case eq of λ ()
 ...   | D.muxInvoked | _ = case eq of λ ()
 ...   | D.muxReturned | _ = case eq of λ ()
 ...   | D.invoked | _ = case eq of λ ()
 ...   | D.returned | _ = case eq of λ ()
 ...   | D.throwing | _ = case eq of λ ()
 return-initiator-preserves : ∀ w s {t} → D.returnInitiator w s ≡ just t → Valid s → Valid t
 return-initiator-preserves w s eq valid with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just observedTicket with D.phase observedTicket | D.initiatorReady w observedTicket s
 ...   | D.muxInvoked | true with D.payload observedTicket
 ...     | Types.protocolCompletion Mux.initiatorJob n gen clean = case just-injective eq of λ { refl → valid }
 ...     | Types.protocolCompletion Mux.initiatorJob n gen (errored err) with R.step (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) in actual
 ...       | nothing = case eq of λ ()
 ...       | just r = case just-injective eq of λ { refl → Raw.step-preserves (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) actual valid }
 return-initiator-preserves w s eq valid | just observedTicket | D.muxInvoked | true | Types.protocolCompletion Mux.responderJob n gen result = case eq of λ ()
 return-initiator-preserves w s eq valid | just observedTicket | D.muxInvoked | true | Types.infraMuxer err = case eq of λ ()
 return-initiator-preserves w s eq valid | just observedTicket | D.muxInvoked | true | Types.infraDemuxer err = case eq of λ ()
 return-initiator-preserves w s eq valid | just observedTicket | D.muxInvoked | false = case eq of λ ()
 return-initiator-preserves w s eq valid | just observedTicket | D.captured | _ = case eq of λ ()
 return-initiator-preserves w s eq valid | just observedTicket | D.muxReturned | _ = case eq of λ ()
 return-initiator-preserves w s eq valid | just observedTicket | D.invoked | _ = case eq of λ ()
 return-initiator-preserves w s eq valid | just observedTicket | D.returned | _ = case eq of λ ()
 return-initiator-preserves w s eq valid | just observedTicket | D.throwing | _ = case eq of λ ()
 step-preserves : ∀ a s {t} → D.step a s ≡ just t → Valid s → Valid t
 step-preserves (D.run a) s eq valid with D.allowed a s
 ... | false = case eq of λ ()
 ... | true with R.step a (D.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just r = case just-injective eq of λ { refl → Raw.step-preserves a (D.base s) actual valid }
 step-preserves (D.beginDeltaQ w) = begin-preserves w
 step-preserves (D.observeReturn w) = complete-preserves w
 step-preserves (D.observeException w result) s eq valid = throw-preserves w result false s eq valid
 step-preserves (D.beginInitiatorTrace w) = begin-initiator-preserves w
 step-preserves (D.observeInitiatorReturn w) = return-initiator-preserves w
 step-preserves (D.observeInitiatorException w result) s eq valid = throw-initiator-preserves w result false s eq valid
 step-preserves (D.deliverShutdown err) s eq valid with Close.phase (W.shutdown (R.base (D.base s))) in awaiting
 ... | Close.awaitDelivery e w with D.faultPlan w (R.async err) s in chosen
 ...   | nothing = case eq of λ ()
 ...   | just p = apply-preserves w p true s eq valid (selection-safe selected valid)
   where selected = DF.fault-selection w (R.async err) s chosen
 step-preserves (D.deliverShutdown err) s eq valid | Close.initial = case eq of λ ()
 step-preserves (D.deliverShutdown err) s eq valid | Close.reading = case eq of λ ()
 step-preserves (D.deliverShutdown err) s eq valid | Close.sendReady e w = case eq of λ ()
 step-preserves (D.deliverShutdown err) s eq valid | Close.awaitResults = case eq of λ ()
 step-preserves (D.deliverShutdown err) s eq valid | Close.closed = case eq of λ ()
 step-preserves (D.deliverInitiatorShutdown err) s eq valid with Close.phase (W.shutdown (R.base (D.base s))) in awaiting
 ... | Close.awaitDelivery e w with D.initiatorFaultPlan w (R.async err) s in chosen
 ...   | nothing = case eq of λ ()
 ...   | just p = apply-preserves w p true s eq valid (selection-safe selected valid)
   where selected = initiator-selection w (R.async err) s chosen
 step-preserves (D.deliverInitiatorShutdown err) s eq valid | Close.initial = case eq of λ ()
 step-preserves (D.deliverInitiatorShutdown err) s eq valid | Close.reading = case eq of λ ()
 step-preserves (D.deliverInitiatorShutdown err) s eq valid | Close.sendReady e w = case eq of λ ()
 step-preserves (D.deliverInitiatorShutdown err) s eq valid | Close.awaitResults = case eq of λ ()
 step-preserves (D.deliverInitiatorShutdown err) s eq valid | Close.closed = case eq of λ ()



-- A selected catch rewrites an existing fault whose owner is already backed.
module Catch (b : ErrorId → Bool)
 (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains b s t → Obs s → Obs t) where
 private module C = CatchModel b using (State; action; allowed; apply; base; canObserve; cancellation; deliverShutdown; initial; observe; observeCancellation; observeException; poolAt; run; select; step; synchronous)
 private module D = DeltaQModel b using (base; delivery; initial; step)
 private module M = MonitorModel b using (failed; finishMatches)
 private module P = ProtocolModel using (muxAt)
 private module R = UnwindModel b using (Fault; async; asyncDead; asyncStatus; awaitingClose; base; closing; enact; faults; handedOff; mux; outcome; phase; poolClosed; protocols; readyBody; readyBuffer; setSource; sync)
 private module W = ExitModel b using (exits; shutdown)
 private module Pool = ProtocolModel.Pool using (cancelPending; closedPool; closing; joinPending; openPool; phase)
 private module Raw = Unwind b Obs stable
 private module Delta = DeltaQ b Obs stable using (Valid; delivery-safe; step-preserves)
 Valid : C.State → Set
 Valid s = Delta.Valid (C.base s)
 selection-safe : ∀ w reason s {p} → C.select w reason s ≡ just p → Valid s → Raw.PlanSafe (C.action p) (D.base (C.base s))
 selection-safe w reason s eq valid with lookup w (R.faults (D.base (C.base s))) in found | Pool.phase (C.poolAt w s) | lookup w (W.exits (R.base (D.base (C.base s))))
 ... | just f | Pool.closedPool | nothing with R.phase f | R.outcome f | P.muxAt (R.mux f) (R.protocols (D.base (C.base s)))
 ...   | R.asyncDead | R.async old | just m with M.finishMatches (M.failed old) (Mux.status m) | C.canObserve reason m s
 ...     | true | true = case just-injective eq of λ { refl → Raw.safe-local }
 ...     | false | _ = case eq of λ ()
 ...     | true | false = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | nothing | R.asyncDead | R.async old | nothing = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | nothing | R.asyncDead | R.sync old | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | nothing | R.readyBody | _ | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | nothing | R.readyBuffer | _ | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | nothing | R.awaitingClose | _ | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | nothing | R.closing | _ | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | nothing | R.poolClosed | _ | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | nothing | R.asyncStatus | _ | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | nothing | R.handedOff | _ | _ = case eq of λ ()
 selection-safe w reason s eq valid | nothing | _ | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.openPool | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closing | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.cancelPending j | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.joinPending j | _ = case eq of λ ()
 selection-safe w reason s eq valid | just f | Pool.closedPool | just ownerFrame = case eq of λ ()
 apply-preserves : ∀ w p ack s {t} → C.apply w p ack s ≡ just t → Valid s → Raw.PlanSafe (C.action p) (D.base (C.base s)) →
   Valid t
 apply-preserves w p ack s eq valid safe with R.enact (D.delivery ack (C.action p)) (D.base (C.base s)) in actual
 ... | nothing = case eq of λ ()
 ... | just r = case just-injective eq of λ { refl → Raw.enact-preserves (D.delivery ack (C.action p)) (D.base (C.base s)) actual valid
   (Delta.delivery-safe ack (C.action p) (D.base (C.base s)) safe) }
 observe-preserves : ∀ w reason ack s {t} → C.observe w reason ack s ≡ just t → Valid s →
   Valid t
 observe-preserves w reason ack s eq valid with C.select w reason s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = apply-preserves w p ack s eq valid (selection-safe w reason s chosen valid)
 step-preserves : ∀ a s {t} → C.step a s ≡ just t → Valid s → Valid t
 step-preserves (C.run a) s eq valid with C.allowed a
 ... | false = case eq of λ ()
 ... | true with D.step a (C.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just d = case just-injective eq of λ { refl → Delta.step-preserves a (C.base s) actual valid }
 step-preserves (C.observeException w err) s eq valid = observe-preserves w (C.synchronous err) false s eq valid
 step-preserves (C.observeCancellation w site err) s eq valid = observe-preserves w (C.cancellation site err) false s eq valid
 step-preserves (C.deliverShutdown site err) s eq valid with Close.phase (W.shutdown (R.base (D.base (C.base s)))) in awaiting
 ... | Close.awaitDelivery e w with C.select w (C.cancellation site err) s in chosen
 ...   | nothing = case eq of λ ()
 ...   | just p = apply-preserves w p true s eq valid (selection-safe w (C.cancellation site err) s chosen valid)
 step-preserves (C.deliverShutdown site err) s eq valid | Close.initial = case eq of λ ()
 step-preserves (C.deliverShutdown site err) s eq valid | Close.reading = case eq of λ ()
 step-preserves (C.deliverShutdown site err) s eq valid | Close.sendReady e w = case eq of λ ()
 step-preserves (C.deliverShutdown site err) s eq valid | Close.awaitResults = case eq of λ ()
 step-preserves (C.deliverShutdown site err) s eq valid | Close.closed = case eq of λ ()



-- Pre-publication transfer derives its physical owner from the selected mux.
module Publication (b : ErrorId → Bool)
 (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains b s t → Obs s → Obs t) where
 private module N = PublicationModel b using (target; State; action; allowed; apply; base; deliverShutdown; deliveryReady; failures; initial; observe; observeFailure; poolAt; raw; run; select; siteReady; source; step)
 private module C = CatchModel b using (base; initial; step)
 private module D = DeltaQModel b using (delivery)
 private module R = UnwindModel b using (async; sync; base; enact; faults; owner; setSource)
 private module W = ExitModel b using (exits; sameStart; shutdown; phase; exitFrame)
 private module U = MuxModel Types.TypedResult using (captured; progress; startup)
 private module Startup = ProtocolModel.Startup using (awaitPublication; bearerReady; bufferReady; demuxerForked; demuxerRegistered; egressReady; matureTraced; monitoring; muxerForked; muxerRegistered; phase; poolReady; published; runEntered; startingTraced)
 private module Pool = ProtocolModel.Pool using (handles)
 private module Raw = Unwind b Obs stable
 private module Delta = DeltaQ b Obs stable using (delivery-safe)
 private module CatchProof = Catch b Obs stable using (Valid; step-preserves)
 Valid : N.State → Set
 Valid s = CatchProof.Valid (N.base s)
 selection : ∀ w site result s {p} → N.select w site result s ≡ just p → Valid s →
   Raw.PlanSafe (N.action p) (N.raw s)
 selection w site result s eq valid with lookup w (N.failures s) | R.owner w (N.raw s) in owner-found | lookup w (W.exits (R.base (N.raw s))) in absent | lookup w (R.faults (N.raw s))
 ... | just oldFault | _ | _ | _ = case eq of λ ()
 ... | nothing | nothing | _ | _ = case eq of λ ()
 ... | nothing | just f | just e | _ = case eq of λ ()
 ... | nothing | just f | nothing | just oldFault = case eq of λ ()
 ... | nothing | just f | nothing | nothing with N.siteReady site f (N.source s) | N.deliveryReady site result | Startup.phase (U.startup f) | Pool.handles (N.poolAt w s)
 ...   | true | true | Startup.awaitPublication | [] with lookup w (Shared.handlers (Machine.world (O.core (N.source s)))) |
    lookup (Shared.handlerPromise (U.captured f)) (Shared.handshakeResults (Machine.world (O.core (N.source s))))
 ...     | just actual | nothing with W.sameStart (U.captured f) actual
 ...       | true = case just-injective eq of λ { refl →
    Raw.safe-transfer }
 ...       | false = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.awaitPublication | [] | nothing | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.awaitPublication | [] | just actual | just value = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | false | _ | _ | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | false | _ | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.awaitPublication | h ∷ rest = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.published | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.bufferReady | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.bearerReady | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.runEntered | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.startingTraced | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.egressReady | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | Startup.poolReady | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | (Startup.muxerForked j) | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | (Startup.muxerRegistered j) | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | (Startup.demuxerForked j k) | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | (Startup.demuxerRegistered j k) | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | (Startup.matureTraced j k) | _ = case eq of λ ()
 selection w site result s eq valid | nothing | just f | nothing | nothing | true | true | (Startup.monitoring j k) | _ = case eq of λ ()
 apply-preserves : ∀ w p ack s {t} → N.apply w p ack s ≡ just t → Valid s →
   Raw.PlanSafe (N.action p) (N.raw s) →
   Valid t
 apply-preserves w p ack s eq valid safe with R.enact (D.delivery ack (N.action p)) (N.raw s) in actual
 ... | nothing = case eq of λ ()
 ... | just r = case just-injective eq of λ { refl → Raw.enact-preserves (D.delivery ack (N.action p)) (N.raw s) actual valid
   (Delta.delivery-safe ack (N.action p) (N.raw s) safe) }
 observe-preserves : ∀ w site result ack s {t} → N.observe w site result ack s ≡ just t → Valid s →
   Valid t
 observe-preserves w site result ack s eq valid with N.select w site result s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = apply-preserves w p ack s eq valid selected
   where selected = selection w site result s chosen valid
 step-preserves : ∀ a s {t} → N.step a s ≡ just t → Valid s → Valid t
 step-preserves (N.run a) s eq valid with N.allowed a s
 ... | false = case eq of λ ()
 ... | true with C.step a (N.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just c = case just-injective eq of λ { refl → CatchProof.step-preserves a (N.base s) actual valid }
 step-preserves (N.observeFailure w site result) s eq valid = observe-preserves w site result false s eq valid
 step-preserves (N.deliverShutdown site err) s eq valid with Close.phase (W.shutdown (R.base (N.raw s))) in awaiting
 ... | Close.awaitDelivery e w with N.select w site (R.async err) s in chosen
 ...   | nothing = case eq of λ ()
 ...   | just p = apply-preserves w p true s eq valid selected
   where selected = selection w site (R.async err) s chosen valid
 step-preserves (N.deliverShutdown site err) s eq valid | Close.initial = case eq of λ ()
 step-preserves (N.deliverShutdown site err) s eq valid | Close.reading = case eq of λ ()
 step-preserves (N.deliverShutdown site err) s eq valid | Close.sendReady e w = case eq of λ ()
 step-preserves (N.deliverShutdown site err) s eq valid | Close.awaitResults = case eq of λ ()
 step-preserves (N.deliverShutdown site err) s eq valid | Close.closed = case eq of λ ()



-- Server bookkeeping retains backing; real physical calls use the lower proof.
module Server (isBearerClosed : ErrorId → Bool)
 (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains isBearerClosed s t → Obs s → Obs t) where
 private module SA = AdmissionModel isBearerClosed using (restoreWorker; workerRestore; raised; returned; scopePlan; socketScopePlan; isAcceptedSocket; closeForkFailure; closeFailedFork; failedForkSocket; Action; State; initial; setSource; source; request; socketOutcome; acceptedFork; accepting; allowed; base; bodyExited; calling; chooseScope; closeDisconnected; closeException; closePrefix; closePrefixWorker; closeWorker; enactClose; enactPrefixClose; enactScope; forkAccepted; fresh; inherit; listenerOpen; nextException; nextNormal; observeException; observeReturn; pc; physicalAction; prefixCloseFailed; prefixException; prefixMatches; prefixReturned; publishWorkerResult; resultAvailable; run; runMachine; sameLimit; scope; scopeAdvance; shared; stage; step; workerClose; workerException; workerPrefixException; workerPrefixReturned; workerResult; workerReturned; workers)
 private module N = PublicationModel isBearerClosed using (initial; raw; step)
 private module W = ExitModel isBearerClosed using (run)
 private module G = GroupModel isBearerClosed using (Action; run)
 private module Monitor = MonitorModel isBearerClosed using (run)
 private module P = ProtocolModel using (run)
 private module U = MuxModel Types.TypedResult using (run)
 private module PublishFacts = Publication isBearerClosed Obs stable using (Valid; step-preserves)
 Valid : SA.State → Set
 Valid s = PublishFacts.Valid (SA.base s)
 -- Successful birth writes an admission and socket; physical metadata is separate.
 fork-preserves : ∀ w req s {t} → SA.forkAccepted w req s ≡ just t → Valid s → Valid t
 fork-preserves w req s eq valid with SA.accepting (SA.stage s) | SA.listenerOpen s |
   SA.sameLimit req (SA.workers s) | SA.fresh w s | SA.fresh (Shared.child req) s |
   w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (SA.shared s))
 ... | true | true | true | true | true | no _ | nothing =
   case just-injective eq of λ { refl → Unwind.source-quiet isBearerClosed Obs stable
     (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
       { admissions = put w (Shared.admissionWorker req Shared.acquireMap) (Shared.admissions (SA.shared s))
       ; sockets = put (Shared.socketRef req) (Shared.admitting w) (Shared.sockets (SA.shared s)) }) })
     (N.raw (SA.base s)) valid }
 ... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
 ... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
 ... | true | true | false | _ | _ | _ | _ = case eq of λ ()
 ... | true | true | true | false | _ | _ | _ = case eq of λ ()
 ... | true | true | true | true | false | _ | _ = case eq of λ ()
 ... | true | true | true | true | true | yes _ | _ = case eq of λ ()
 ... | true | true | true | true | true | no _ | just _ = case eq of λ ()

 -- Return, exception and result observations change only raw-worker metadata.
 return-preserves : ∀ w s {t} → SA.observeReturn w s ≡ just t → Valid s → Valid t
 return-preserves w s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.completedHandshake (Shared.connected _) = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.completedHandshake (Shared.disconnected _) = case just-injective eq of λ { refl → valid }
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
 return-preserves w s eq valid | nothing | _ = case eq of λ ()
 return-preserves w s eq valid | just _ | nothing = case eq of λ ()
 prefix-return-preserves : ∀ w s {t} → SA.prefixReturned w s ≡ just t → Valid s → Valid t
 prefix-return-preserves w s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.closeSocket Shared.hardLimitReached = case just-injective eq of λ { refl → valid }
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
 ...   | SA.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket Shared.forbidden = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket Shared.forkFailed = case eq of λ ()
 ...   | SA.closeDisconnected | _ = case eq of λ ()
 ...   | SA.closeException _ | _ = case eq of λ ()
 ...   | SA.closePrefix _ _ | _ = case eq of λ ()
 ...   | SA.bodyExited _ | _ = case eq of λ ()
 ...   | SA.resultAvailable _ | _ = case eq of λ ()
 prefix-return-preserves w s eq valid | nothing | _ = case eq of λ ()
 prefix-return-preserves w s eq valid | just _ | nothing = case eq of λ ()
 prefix-exception-preserves : ∀ w err s {t} → SA.prefixException w err s ≡ just t → Valid s → Valid t
 prefix-exception-preserves w err s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket Shared.forbidden = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.closeSocket Shared.forkFailed = case just-injective eq of λ { refl → valid }
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
 prefix-exception-preserves w err s eq valid | nothing | _ = case eq of λ ()
 prefix-exception-preserves w err s eq valid | just _ | nothing = case eq of λ ()
 exception-preserves : ∀ w err s {t} → SA.observeException w err s ≡ just t → Valid s → Valid t
 exception-preserves w err s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.acquireMap = case eq of λ ()
 ...   | SA.calling | Shared.count _ = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.prepare _ = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.selectEntry _ _ = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.forkHandler _ _ _ = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.publish _ _ _ = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket _ = case eq of λ ()
 ...   | SA.calling | Shared.finished _ = case eq of λ ()
 ...   | SA.calling | Shared.countPublished _ _ = case just-injective eq of λ { refl → valid }
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
 exception-preserves w err s eq valid | nothing | _ = case eq of λ ()
 exception-preserves w err s eq valid | just _ | nothing = case eq of λ ()
 result-preserves : ∀ w s {t} → SA.publishWorkerResult w s ≡ just t → Valid s → Valid t
 result-preserves w s eq valid with lookup w (SA.workers s)
 ... | nothing = case eq of λ ()
 ... | just worker with SA.pc worker
 ...   | SA.bodyExited r = case just-injective eq of λ { refl → valid }
 ...   | SA.calling = case eq of λ ()
 ...   | SA.closeDisconnected = case eq of λ ()
 ...   | SA.closeException _ = case eq of λ ()
 ...   | SA.closePrefix _ _ = case eq of λ ()
 ...   | SA.resultAvailable _ = case eq of λ ()

 -- Both successful/uncertain socket observations preserve the capture map.
 enact-close-preserves : ∀ w worker outcome next s → Valid s →
   Valid (SA.enactClose w worker outcome next s)
 enact-close-preserves w worker outcome next s valid = Unwind.source-quiet isBearerClosed Obs stable
   (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
     { sockets = put (Shared.socketRef (SA.request worker)) (SA.socketOutcome outcome) (Shared.sockets (SA.shared s)) }) })
   (N.raw (SA.base s)) valid
 -- The failed bare fork's close changes only the captured socket cell.
 fork-close-preserves : ∀ outcome s {t} → SA.closeFailedFork outcome s ≡ just t → Valid s → Valid t
 fork-close-preserves outcome s eq valid with SA.failedForkSocket s
 ... | nothing = case eq of λ ()
 ... | just sock with SA.isAcceptedSocket sock s
 ...   | false = case eq of λ ()
 ...   | true = case just-injective eq of λ { refl → Unwind.source-quiet isBearerClosed Obs stable
   (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
     { sockets = put sock (SA.socketOutcome outcome) (Shared.sockets (SA.shared s)) }) })
   (N.raw (SA.base s)) valid }
 enact-prefix-preserves : ∀ w worker result outcome s {t} → SA.enactPrefixClose w worker result outcome s ≡ just t →
   Valid s → Valid t
 enact-prefix-preserves w worker result nothing s eq valid with N.step
   (SA.runMachine (Machine.admissionStep w Admission.close)) (SA.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just n = case just-injective eq of λ { refl → PublishFacts.step-preserves (SA.runMachine (Machine.admissionStep w Admission.close)) (SA.base s) advanced valid }
 enact-prefix-preserves w worker result (just err) s eq valid = case just-injective eq of λ
   { refl → enact-close-preserves w worker (just err) (SA.prefixCloseFailed result err) s valid }
 close-prefix-preserves : ∀ w worker failure result outcome s {t} →
   SA.closePrefixWorker w worker failure result outcome s ≡ just t → Valid s → Valid t
 close-prefix-preserves w worker failure result outcome s eq valid with SA.prefixMatches w failure s
 ... | false = case eq of λ ()
 ... | true = enact-prefix-preserves w worker result outcome s eq valid
 close-preserves : ∀ w outcome s {t} → SA.closeWorker w outcome s ≡ just t → Valid s → Valid t
 close-preserves w outcome s eq valid with lookup w (SA.workers s)
 ... | nothing = case eq of λ ()
 ... | just worker with SA.pc worker
 ...   | SA.closeDisconnected = case just-injective eq of λ
   { refl → enact-close-preserves w worker outcome (SA.nextNormal outcome) s valid }
 ...   | SA.closeException err = case just-injective eq of λ
   { refl → enact-close-preserves w worker outcome (SA.nextException err outcome) s valid }
 ...   | SA.closePrefix f r = close-prefix-preserves w worker f r outcome s eq valid
 ...   | SA.calling = case eq of λ ()
 ...   | SA.bodyExited _ = case eq of λ ()
 ...   | SA.resultAvailable _ = case eq of λ ()
 inherit-preserves : ∀ a s {t} → SA.inherit a s ≡ just t → Valid s → Valid t
 inherit-preserves a s eq valid with SA.allowed a s
 ... | false = case eq of λ ()
 ... | true with N.step a (SA.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just n = case just-injective eq of λ { refl → PublishFacts.step-preserves a (SA.base s) actual valid }
 body-restore-preserves : ∀ w s {t} → SA.restoreWorker w s ≡ just t → Valid s → Valid t
 body-restore-preserves w s eq valid with lookup w (SA.workers s)
 ... | nothing = case eq of λ ()
 ... | just worker with SA.pc worker
 ...   | SA.closePrefix Shared.bodyFailed (SA.raised fault) with N.step (SA.runMachine (Machine.admissionStep w Admission.restoreBody)) (SA.base s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just n = case just-injective eq of λ { refl → PublishFacts.step-preserves (SA.runMachine (Machine.admissionStep w Admission.restoreBody)) (SA.base s) actual valid }
 body-restore-preserves w s eq valid | just worker | SA.calling = case eq of λ ()
 body-restore-preserves w s eq valid | just worker | SA.closeDisconnected = case eq of λ ()
 body-restore-preserves w s eq valid | just worker | SA.closeException fault = case eq of λ ()
 body-restore-preserves w s eq valid | just worker | SA.closePrefix Shared.hardLimitReached result = case eq of λ ()
 body-restore-preserves w s eq valid | just worker | SA.closePrefix Shared.forbidden result = case eq of λ ()
 body-restore-preserves w s eq valid | just worker | SA.closePrefix Shared.forkFailed result = case eq of λ ()
 body-restore-preserves w s eq valid | just worker | SA.closePrefix Shared.bodyFailed SA.returned = case eq of λ ()
 body-restore-preserves w s eq valid | just worker | SA.bodyExited result = case eq of λ ()
 body-restore-preserves w s eq valid | just worker | SA.resultAvailable result = case eq of λ ()

 scope-enact-preserves : ∀ p s {t} → SA.enactScope p s ≡ just t → Valid s → Valid t
 scope-enact-preserves (SA.scopePlan st keep ig action) s eq valid with action
 ... | nothing = case just-injective eq of λ { refl → valid }
 ... | just command with N.step command (SA.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just n = case just-injective eq of λ { refl → PublishFacts.step-preserves command (SA.base s) actual valid }
 scope-enact-preserves (SA.socketScopePlan st keep ig sock owner) s eq valid =
   case just-injective eq of λ { refl → Unwind.source-quiet isBearerClosed Obs stable
     (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
     { sockets = put sock owner (Shared.sockets (SA.shared s)) }) })
     (N.raw (SA.base s)) valid }
 scope-preserves : ∀ a s {t} → SA.scopeAdvance a s ≡ just t → Valid s → Valid t
 scope-preserves a s eq valid with SA.chooseScope a s
 ... | nothing = case eq of λ ()
 ... | just p = scope-enact-preserves p s eq valid
 step-preserves : ∀ a s {t} → SA.step a s ≡ just t → Valid s → Valid t
 step-preserves (SA.closeForkFailure outcome) = fork-close-preserves outcome
 step-preserves (SA.acceptedFork w req) = fork-preserves w req
 step-preserves (SA.workerRestore w) = body-restore-preserves w
 step-preserves (SA.run a) = inherit-preserves a
 step-preserves (SA.workerReturned w) = return-preserves w
 step-preserves (SA.workerPrefixReturned w) = prefix-return-preserves w
 step-preserves (SA.workerPrefixException w err) = prefix-exception-preserves w err
 step-preserves (SA.workerException w err) = exception-preserves w err
 step-preserves (SA.workerClose w outcome) = close-preserves w outcome
 step-preserves (SA.workerResult w) = result-preserves w
 step-preserves (SA.scope a) = scope-preserves a


-- IG exit plans delegate physical changes or update only their own metadata.
module IGExit (b : ErrorId → Bool)
 (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains b s t → Obs s → Obs t) where
 private module E = IGExitModel b using (clearPending; source; State; abandon; ownFailure; base; choose; delegate; enact; finish; initial; local; step)
 private module SA = AdmissionModel b using (restoreWorker; workerRestore; raised; returned; scopePlan; socketScopePlan; isAcceptedSocket; closeForkFailure; closeFailedFork; failedForkSocket; initial; setSource; step; base)
 private module N = PublicationModel b using (raw)
 private module ServerFacts = Server b Obs stable using (Valid; step-preserves)
 Valid : E.State → Set
 Valid s = ServerFacts.Valid (E.base s)
 enact-preserves : ∀ p s {t} → E.enact p s ≡ just t → Valid s → Valid t
 enact-preserves (E.delegate a e) s eq valid with SA.step a (E.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just server = case just-injective eq of λ { refl → ServerFacts.step-preserves a (E.base s) actual valid }
 enact-preserves (E.local e) s eq valid = case just-injective eq of λ { refl → valid }
 enact-preserves (E.abandon r) s eq valid = case just-injective eq of λ { refl →
   Unwind.source-quiet b Obs stable (E.clearPending (E.source s)) (N.raw (SA.base (E.base s))) valid }
 enact-preserves (E.ownFailure r f) s eq valid = case just-injective eq of λ { refl →
   Unwind.source-quiet b Obs stable (E.clearPending (E.source s)) (N.raw (SA.base (E.base s))) valid }
 enact-preserves (E.finish e) s eq valid = case just-injective eq of λ { refl → valid }
 step-preserves : ∀ a s {t} → E.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with E.choose a s
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid


-- The shared composition routes every CM write through the actual Server step.
module SharedLayer (b io : ErrorId → Bool)
 (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains b s t → Obs s → Obs t) where
 private module K = SharedModel b io using (State; coreAction; coreAllowed; coreStep; initial; peerAllowed; peerOpen; peerStep; peers; server; serverAllowed; serverStep; setSource; step)
 private module E = IGExitModel b using (initial; step)
 private module PS = PeerModel io using (cm; step)
 private module ExitFacts = IGExit b Obs stable using (Valid; step-preserves)
 private module PeerFacts = CleanupPeers io using (cleanups-same)
 private module Raw = Unwind b Obs stable
 private module SA = AdmissionModel b using (restoreWorker; workerRestore; raised; returned; scopePlan; socketScopePlan; isAcceptedSocket; closeForkFailure; closeFailedFork; failedForkSocket; base)
 private module EX = IGExitModel b using (base)
 private module N = PublicationModel b using (raw)
 unwind : K.State → UnwindModel.State b
 unwind s = N.raw (SA.base (EX.base (K.server s)))
 Valid : K.State → Set
 Valid s = ExitFacts.Valid (K.server s)
 step-preserves : ∀ a s {t} → K.step a s ≡ just t → Valid s → Valid t
 step-preserves (K.serverStep a) s eq valid with K.serverAllowed a s
 ... | false = case eq of λ ()
 ... | true with E.step a (K.server s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just e = case just-injective eq of λ { refl → ExitFacts.step-preserves a (K.server s) actual valid }
 step-preserves (K.coreStep a) s eq valid with K.coreAllowed a s
 ... | false = case eq of λ ()
 ... | true with E.step (K.coreAction a) (K.server s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just e = case just-injective eq of λ { refl → ExitFacts.step-preserves (K.coreAction a) (K.server s) actual valid }
 step-preserves (K.peerStep a) s eq valid with K.peerOpen s | K.peerAllowed a s in allowed
 ... | false | _ = case eq of λ ()
 ... | true | false = case eq of λ ()
 ... | true | true with PS.step a (K.peers s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → Raw.source-quiet (PeerModel.cm io p) (unwind s) valid }
