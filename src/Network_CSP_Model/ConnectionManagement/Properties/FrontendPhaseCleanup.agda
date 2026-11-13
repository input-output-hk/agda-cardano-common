{-# OPTIONS --guardedness #-}

-- Phase/cleanup validity through the real frontend (CM-I4c, stage C3). The
-- DeltaQ, catch and publication layers install startup faults and exit frames
-- only through the startup-unwind plans; server admission, IG exit and the
-- shared layer delegate physical changes; permitted peer actions leave the
-- cleanup store unchanged; and the top-level runtime's own fault, coordinator
-- and pool writes are covered by the startup-unwind plan safety.
module ConnectionManagement.Properties.FrontendPhaseCleanup where

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
open import ConnectionManagement.Properties.MuxPhaseCleanup using (present; module Unwind; module Exit)

-- DeltaQ callbacks run actual lower steps or select a startup fault.
module DeltaQ (b : ErrorId → Bool) where
 private module D = DeltaQModel b using (State; allowed; applyFault; base; begin; beginDeltaQ; beginInitiator; beginInitiatorTrace; captured; complete; deliverInitiatorShutdown; deliverShutdown; delivery; entryPhase; faultPlan; finishAction; initial; initiatorFaultPlan; initiatorReady; invoked; muxInvoked; muxReturned; observeException; observeInitiatorException; observeInitiatorReturn; observeReturn; payload; phase; ready; returnInitiator; returned; run; step; throw; throwInitiator; throwing; tickets; wrapMonitor)
 private module M = MonitorModel b using (finishProtocolTrace)
 private module R = UnwindModel b using (Fault; async; base; enact; faults; initial; poolBody; setSource; step)
 private module W = ExitModel b using (shutdown)
 private module Raw = Unwind b
 private module F = UnwindFacts b using (Selection; selection-observation)
 private module DF = DeltaFacts b using (fault-selection)
 Valid : D.State → Set
 Valid s = Raw.Valid (D.base s)
 selection-safe : ∀ {w result route s p} → F.Selection w result route s p → Raw.Valid s → Raw.PlanSafe p s
 selection-safe {w} {result} {route} {s} selected valid rewrite F.Selection.plan-shape selected = Raw.safe-local
   (Raw.ff-put w _ s (cong present (F.Selection.owner-found selected)) valid)
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
 initialized-valid : ∀ c {s} → D.initial c ≡ just s → Valid s
 initialized-valid c eq with R.initial c in lower
 ... | nothing = case eq of λ ()
 ... | just r = case just-injective eq of λ { refl → Raw.initialized-valid c lower }


-- A selected catch rewrites an existing fault whose owner is already backed.
module Catch (b : ErrorId → Bool) where
 private module C = CatchModel b using (State; action; allowed; apply; base; canObserve; cancellation; deliverShutdown; initial; observe; observeCancellation; observeException; poolAt; run; select; step; synchronous)
 private module D = DeltaQModel b using (base; delivery; initial; step)
 private module M = MonitorModel b using (failed; finishMatches)
 private module P = ProtocolModel using (muxAt)
 private module R = UnwindModel b using (Fault; async; asyncDead; asyncStatus; awaitingClose; base; closing; enact; faults; handedOff; mux; outcome; phase; poolClosed; protocols; readyBody; readyBuffer; setSource; sync)
 private module W = ExitModel b using (exits; shutdown)
 private module Pool = ProtocolModel.Pool using (cancelPending; closedPool; closing; joinPending; openPool; phase)
 private module Raw = Unwind b
 private module Delta = DeltaQ b using (Valid; delivery-safe; initialized-valid; step-preserves)
 Valid : C.State → Set
 Valid s = Delta.Valid (C.base s)
 selection-safe : ∀ w reason s {p} → C.select w reason s ≡ just p → Valid s → Raw.PlanSafe (C.action p) (D.base (C.base s))
 selection-safe w reason s eq valid with lookup w (R.faults (D.base (C.base s))) in found | Pool.phase (C.poolAt w s) | lookup w (W.exits (R.base (D.base (C.base s))))
 ... | just f | Pool.closedPool | nothing with R.phase f | R.outcome f | P.muxAt (R.mux f) (R.protocols (D.base (C.base s)))
 ...   | R.asyncDead | R.async old | just m with M.finishMatches (M.failed old) (Mux.status m) | C.canObserve reason m s
 ...     | true | true = case just-injective eq of λ { refl → Raw.safe-local
   (Raw.ff-put w _ (D.base (C.base s)) (Raw.fault-framed (D.base (C.base s)) valid found) valid) }
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
 initialized-valid : ∀ c {s} → C.initial c ≡ just s → Valid s
 initialized-valid c eq with D.initial c in lower
 ... | nothing = case eq of λ ()
 ... | just d = case just-injective eq of λ { refl → Delta.initialized-valid c lower }


-- Pre-publication transfer derives its physical owner from the selected mux.
module Publication (b : ErrorId → Bool) where
 private module N = PublicationModel b using (target; State; action; allowed; apply; base; deliverShutdown; deliveryReady; failures; initial; observe; observeFailure; poolAt; raw; run; select; siteReady; source; step)
 private module C = CatchModel b using (base; initial; step)
 private module D = DeltaQModel b using (delivery)
 private module R = UnwindModel b using (async; sync; base; enact; faults; owner; setSource)
 private module W = ExitModel b using (exits; sameStart; shutdown; phase; exitFrame)
 private module U = MuxModel Types.TypedResult using (captured; progress; startup)
 target-pre : ∀ result h c → c ≡ nothing → Exit.ExitExpected b (λ _ → false) (W.phase (W.exitFrame h (N.target result) nothing)) c
 target-pre (R.sync err) h c none = none
 target-pre (R.async err) h c none = none
 private module Startup = ProtocolModel.Startup using (awaitPublication; bearerReady; bufferReady; demuxerForked; demuxerRegistered; egressReady; matureTraced; monitoring; muxerForked; muxerRegistered; phase; poolReady; published; runEntered; startingTraced)
 private module Pool = ProtocolModel.Pool using (handles)
 private module Raw = Unwind b
 private module Delta = DeltaQ b using (delivery-safe)
 private module CatchProof = Catch b using (Valid; initialized-valid; step-preserves)
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
    Raw.safe-transfer (cong present owner-found) absent (target-pre result (U.captured f)) (Raw.ff-same (N.raw s) valid) }
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
 initialized-valid : ∀ c {s} → N.initial c ≡ just s → Valid s
 initialized-valid c eq with C.initial c in lower
 ... | nothing = case eq of λ ()
 ... | just caught = case just-injective eq of λ { refl → CatchProof.initialized-valid c lower }


-- Server bookkeeping retains backing; real physical calls use the lower proof.
module Server (isBearerClosed : ErrorId → Bool) where
 private module SA = AdmissionModel isBearerClosed using (restoreWorker; workerRestore; raised; returned; scopePlan; socketScopePlan; isAcceptedSocket; closeForkFailure; closeFailedFork; failedForkSocket; Action; State; initial; setSource; source; request; socketOutcome; acceptedFork; accepting; allowed; base; bodyExited; calling; chooseScope; closeDisconnected; closeException; closePrefix; closePrefixWorker; closeWorker; enactClose; enactPrefixClose; enactScope; forkAccepted; fresh; inherit; listenerOpen; nextException; nextNormal; observeException; observeReturn; pc; physicalAction; prefixCloseFailed; prefixException; prefixMatches; prefixReturned; publishWorkerResult; resultAvailable; run; runMachine; sameLimit; scope; scopeAdvance; shared; stage; step; workerClose; workerException; workerPrefixException; workerPrefixReturned; workerResult; workerReturned; workers)
 private module N = PublicationModel isBearerClosed using (initial; raw; step)
 private module W = ExitModel isBearerClosed using (run)
 private module G = GroupModel isBearerClosed using (Action; run)
 private module Monitor = MonitorModel isBearerClosed using (run)
 private module P = ProtocolModel using (run)
 private module U = MuxModel Types.TypedResult using (run)
 private module PublishFacts = Publication isBearerClosed using (Valid; initialized-valid; step-preserves)
 Valid : SA.State → Set
 Valid s = PublishFacts.Valid (SA.base s)
 -- Successful birth writes an admission and socket; physical metadata is separate.
 fork-preserves : ∀ w req s {t} → SA.forkAccepted w req s ≡ just t → Valid s → Valid t
 fork-preserves w req s eq valid with SA.accepting (SA.stage s) | SA.listenerOpen s |
   SA.sameLimit req (SA.workers s) | SA.fresh w s | SA.fresh (Shared.child req) s |
   w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (SA.shared s))
 ... | true | true | true | true | true | no _ | nothing =
   case just-injective eq of λ { refl → Unwind.source-quiet isBearerClosed
     (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
       { admissions = put w (Shared.admissionWorker req Shared.acquireMap) (Shared.admissions (SA.shared s))
       ; sockets = put (Shared.socketRef req) (Shared.admitting w) (Shared.sockets (SA.shared s)) }) })
     (N.raw (SA.base s)) refl valid }
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
 enact-close-preserves w worker outcome next s valid = Unwind.source-quiet isBearerClosed
   (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
     { sockets = put (Shared.socketRef (SA.request worker)) (SA.socketOutcome outcome) (Shared.sockets (SA.shared s)) }) })
   (N.raw (SA.base s)) refl valid
 -- The failed bare fork's close changes only the captured socket cell.
 fork-close-preserves : ∀ outcome s {t} → SA.closeFailedFork outcome s ≡ just t → Valid s → Valid t
 fork-close-preserves outcome s eq valid with SA.failedForkSocket s
 ... | nothing = case eq of λ ()
 ... | just sock with SA.isAcceptedSocket sock s
 ...   | false = case eq of λ ()
 ...   | true = case just-injective eq of λ { refl → Unwind.source-quiet isBearerClosed
   (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
     { sockets = put sock (SA.socketOutcome outcome) (Shared.sockets (SA.shared s)) }) })
   (N.raw (SA.base s)) refl valid }
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
   case just-injective eq of λ { refl → Unwind.source-quiet isBearerClosed
     (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
     { sockets = put sock owner (Shared.sockets (SA.shared s)) }) })
     (N.raw (SA.base s)) refl valid }
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
 initialized-valid : ∀ c {s} → SA.initial c ≡ just s → Valid s
 initialized-valid c eq with Shared.admissions (Machine.world (O.core c)) | Shared.sockets (Machine.world (O.core c)) | N.initial c in lower
 ... | [] | [] | just n = case just-injective eq of λ { refl → PublishFacts.initialized-valid c lower }
 ... | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | nothing = case eq of λ ()

-- IG exit plans delegate physical changes or update only their own metadata.
module IGExit (b : ErrorId → Bool) where
 private module E = IGExitModel b using (clearPending; source; State; abandon; ownFailure; base; choose; delegate; enact; finish; initial; local; step)
 private module SA = AdmissionModel b using (restoreWorker; workerRestore; raised; returned; scopePlan; socketScopePlan; isAcceptedSocket; closeForkFailure; closeFailedFork; failedForkSocket; initial; setSource; step; base)
 private module N = PublicationModel b using (raw)
 private module ServerFacts = Server b using (Valid; initialized-valid; step-preserves)
 Valid : E.State → Set
 Valid s = ServerFacts.Valid (E.base s)
 enact-preserves : ∀ p s {t} → E.enact p s ≡ just t → Valid s → Valid t
 enact-preserves (E.delegate a e) s eq valid with SA.step a (E.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just server = case just-injective eq of λ { refl → ServerFacts.step-preserves a (E.base s) actual valid }
 enact-preserves (E.local e) s eq valid = case just-injective eq of λ { refl → valid }
 enact-preserves (E.abandon r) s eq valid = case just-injective eq of λ { refl →
   Unwind.source-quiet b (E.clearPending (E.source s)) (N.raw (SA.base (E.base s))) refl valid }
 enact-preserves (E.ownFailure r f) s eq valid = case just-injective eq of λ { refl →
   Unwind.source-quiet b (E.clearPending (E.source s)) (N.raw (SA.base (E.base s))) refl valid }
 enact-preserves (E.finish e) s eq valid = case just-injective eq of λ { refl → valid }
 step-preserves : ∀ a s {t} → E.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with E.choose a s
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid
 initialized-valid : ∀ c {s} → E.initial c ≡ just s → Valid s
 initialized-valid c eq with Machine.inboundRelease (O.core c) | Machine.remoteCall (O.core c) | SA.initial c in lower
 ... | nothing | nothing | just a = case just-injective eq of λ { refl → ServerFacts.initialized-valid c lower }
 ... | just _ | _ | _ = case eq of λ ()
 ... | nothing | just _ | _ = case eq of λ ()
 ... | nothing | nothing | nothing = case eq of λ ()

-- The shared composition routes every CM write through the actual Server step.
module SharedLayer (b io : ErrorId → Bool) where
 private module K = SharedModel b io using (State; coreAction; coreAllowed; coreStep; initial; peerAllowed; peerOpen; peerStep; peers; server; serverAllowed; serverStep; setSource; step)
 private module E = IGExitModel b using (initial; step)
 private module PS = PeerModel io using (cm; step)
 private module ExitFacts = IGExit b using (Valid; initialized-valid; step-preserves)
 private module PeerFacts = CleanupPeers io using (cleanups-same)
 private module Permission = OriginRuntime.Frontend b io (λ _ _ → false) using (peer-permission)
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
 ...   | just p = case just-injective eq of λ { refl → Unwind.source-quiet b (PS.cm p) (unwind s)
   (PeerFacts.cleanups-same a (K.peers s) (Permission.peer-permission a s allowed) actual) valid }
 initialized-valid : ∀ c g {s} → K.initial c g ≡ just s → Valid s
 initialized-valid c g eq with E.initial c in lower
 ... | nothing = case eq of λ ()
 ... | just e = case just-injective eq of λ { refl → ExitFacts.initialized-valid c lower }


open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_)
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Subsystem as Sub
import Data.Nat as Nat

-- Frontend selection supplies the certificates needed by its direct metadata writes.
module Frontend (b io : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) where
 private module T = SharedModel.Protocols b io canInitiate using (Plan; Runs; Runtime; advance; allClean; base; birth; byThread; cacheResult; caller; calls; choose; cleanObservation; command; commitClean; commitError; complete; completionPlan; controllerFree; cursor; deliverStartTraceShutdown; deliverTraceFault; descriptor; dispatch; enact; failedC; firstPeer; forkPlan; forkReadyC; forkStart; front; group; handleRef; idle; idleC; inherit; inheritAllowed; initialize; invokeStartTrace; latest; local; more; mux; nextRequest; observeStartTraceException; owner; peer; peerRef; pending; physical; pollResults; pollResultsPlan; protocol; publication; readAllowed; reading; registerPlan; registerStart; registeringC; returnStartTrace; selectPlan; selectStart; selectedC; slotIdle; startNext; startTraceSelection; stop; thread; traceFault; tracingC; value; waitAction; waitJobPlan; waitJobResults; waitMonitorPlan; waitMonitorResults; waitResults; worker)
 private module K = SharedModel b io using (context; initial; peerOpen; peers; server; step)
 private module PS = PeerModel io using (cm; step)
 private module C = PeerContext io using (SubContext; subsystem)
 private module N = PublicationModel b using (raw)
 private module G = GroupModel b using (base)
 private module Monitor = MonitorModel b using (ownerContext)
 private module R = UnwindModel b using (State; acknowledge; async; base; inherited; local; machine; pool; poolBody; start; transfer)
 private module W = ExitModel b using (control; physical; shutdown)
 private module U = MuxModel Types.TypedResult using (frames)
 private module P = ProtocolModel using (base; fresh; generationFresh; jobs; muxAt; noParent; noResults; poolAt)
 private module Pool = ProtocolModel.Pool using (cancelPending; closedPool; closing; fork; joinPending; openPool; phase; step)
 private module S = AdmissionModel b using (inCMClose; stage)
 private module E = IGExitModel b using (base)
 private module Raw = Unwind b
 private module Combined = SharedLayer b io using (Valid; initialized-valid; step-preserves)
 private module PeerFacts = CleanupPeers io using (cleanups-same)
 private module Origin = OriginPeers io using (Allowed)
 private module F = UnwindFacts b using (Selection; selection-observation)
 private module Delta = DeltaQ b using (selection-safe)
 Valid : T.Runtime → Set
 Valid s = Combined.Valid (T.base s)
 unwind : T.Runtime → R.State
 unwind s = N.raw (T.publication (T.base s))
 cache-valid : ∀ rid r result f s → Combined.Valid s → Combined.Valid (T.cacheResult rid r result f s)
 cache-valid rid r result f s valid with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
 ... | nothing = valid
 ... | just (current , _) with current ≟ rid
 ...   | no _ = valid
 ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context s)))
 ...     | nothing = valid
 ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
 ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
 ...         | nothing = valid
 ...         | just rs = valid
 cache-valid rid r result f s valid | just (current , _) | yes _ | just peer | no _ | _ = valid
 cache-valid rid r result f s valid | just (current , _) | yes _ | just peer | yes _ | no _ = valid
 -- Special plans retain their actual selector evidence. An arbitrary plan can
 -- replace fault/shutdown metadata, so preservation is proved for chosen plans.
 SafePlan : T.Plan → T.Runtime → Set
 SafePlan (T.birth w ownerFrame pool j rid r f) s = Raw.framedR (unwind s) w ≡ true
 SafePlan (T.caller a f) s = Origin.Allowed a
 SafePlan (T.traceFault w rid result fs) s = Raw.PlanSafe (R.local fs) (unwind s)
 SafePlan (T.deliverTraceFault w rid result fs coordinator) s = Raw.PlanSafe (R.local fs) (unwind s)
 SafePlan _ s = ⊤
 local-safe : ∀ fs s → Raw.PlanSafe (R.local fs) (unwind s) → Raw.Valid (unwind s) → Raw.Valid (record (unwind s) { faults = fs })
 local-safe fs s safe valid = Raw.enact-preserves (R.local fs) (unwind s) refl valid safe
 enact-preserves : ∀ p s {t} → T.enact p s ≡ just t → Valid s → SafePlan p s → Valid t
 enact-preserves (T.inherit a f) s eq valid safe with K.step a (T.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just k = case just-injective eq of λ { refl → Combined.step-preserves a (T.base s) actual valid }
 enact-preserves (T.caller a f) s eq valid safe with PS.step a (K.peers (T.base s)) in actual
 ... | nothing = case eq of λ ()
 ... | just peer = case just-injective eq of λ { refl → Raw.source-quiet (PS.cm peer) (unwind s)
   (PeerFacts.cleanups-same a (K.peers (T.base s)) safe actual) valid }
 enact-preserves (T.local f) s eq valid safe = case just-injective eq of λ { refl → valid }
 enact-preserves (T.reading r) s eq valid safe = case just-injective eq of λ { refl → valid }
 enact-preserves (T.traceFault w rid result fs) s eq valid safe = case just-injective eq of λ { refl → local-safe fs s safe valid }
 enact-preserves (T.deliverTraceFault w rid result fs coordinator) s eq valid safe = case just-injective eq of λ { refl →
   Raw.shutdown-quiet coordinator (record (unwind s) { faults = fs }) (local-safe fs s safe valid) }
 enact-preserves (T.birth w ownerFrame pool j rid r f) s eq valid safe = case just-injective eq of λ { refl →
   -- The job-table write is invisible to every validity field.
   let pooled = Raw.pool-valid w ownerFrame pool (unwind s) safe valid in Exit.exit-valid (Exit.lower pooled) (Exit.exits-ok pooled) }
 enact-preserves (T.complete a rid r result) s eq valid safe with K.step a (T.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just k = case just-injective eq of λ { refl → cache-valid rid r result (T.front s) k (Combined.step-preserves a (T.base s) actual valid) }

 trace-selection-start : ∀ w result s {rid fs} →
   T.startTraceSelection w result s ≡ just (rid , fs) →
   R.start w result (λ _ _ → just R.poolBody) (unwind s) ≡ just (R.local fs)
 trace-selection-start w result s eq with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
   Monitor.ownerContext w (G.base (T.group (T.base s)))
 ... | T.tracingC r₀ | true | just (f , mid) with lookup r₀ (T.calls (T.front s))
 ...   | just invocation with T.owner invocation ≟ w | T.mux invocation ≟ mid | T.thread invocation | T.value invocation
 ...     | yes _ | yes _ | nothing | nothing with R.start w result (λ _ _ → just R.poolBody) (unwind s) in started
 ...       | nothing = case eq of λ ()
 ...       | just (R.local selected) = case just-injective eq of λ { refl → refl }
 ...       | just (R.machine action selected) = case eq of λ ()
 ...       | just (R.pool owner ownerFrame action selected) = case eq of λ ()
 ...       | just (R.inherited action) = case eq of λ ()
 ...       | just (R.transfer owner ownerFrame selected) = case eq of λ ()
 ...       | just (R.acknowledge plan) = case eq of λ ()
 trace-selection-start w result s eq | T.tracingC r₀ | true | just (f , mid) | just invocation | no _ | _ | _ | _ = case eq of λ ()
 trace-selection-start w result s eq | T.tracingC r₀ | true | just (f , mid) | just invocation | yes _ | no _ | _ | _ = case eq of λ ()
 trace-selection-start w result s eq | T.tracingC r₀ | true | just (f , mid) | just invocation | yes _ | yes _ | just _ | _ = case eq of λ ()
 trace-selection-start w result s eq | T.tracingC r₀ | true | just (f , mid) | just invocation | yes _ | yes _ | nothing | just _ = case eq of λ ()
 trace-selection-start w result s eq | T.tracingC r₀ | true | just (f , mid) | nothing = case eq of λ ()
 trace-selection-start w result s eq | T.tracingC r₀ | false | _ = case eq of λ ()
 trace-selection-start w result s eq | T.tracingC r₀ | true | nothing = case eq of λ ()
 trace-selection-start w result s eq | T.idleC | _ | _ = case eq of λ ()
 trace-selection-start w result s eq | T.selectedC _ | _ | _ = case eq of λ ()
 trace-selection-start w result s eq | T.forkReadyC _ | _ | _ = case eq of λ ()
 trace-selection-start w result s eq | T.registeringC _ _ | _ | _ = case eq of λ ()
 trace-selection-start w result s eq | T.failedC _ _ | _ | _ = case eq of λ ()

 trace-selection : ∀ w result s {rid fs} →
   T.startTraceSelection w result s ≡ just (rid , fs) →
   F.Selection w result (λ _ _ → just R.poolBody) (unwind s) (R.local fs)
 trace-selection w result s selected = F.selection-observation w result (λ _ _ → just R.poolBody)
   (unwind s) (trace-selection-start w result s selected)

 trace-selection-safe : ∀ w result s {rid fs} →
   T.startTraceSelection w result s ≡ just (rid , fs) → Raw.Valid (unwind s) →
   Raw.PlanSafe (R.local fs) (unwind s)
 trace-selection-safe w result s selected valid = Delta.selection-safe (trace-selection w result s selected) valid

 fork-safe : ∀ w j s p → T.forkPlan w j s ≡ just p → Valid s → SafePlan p s
 fork-safe w j s p eq valid with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
   lookup w (U.frames (P.base (T.physical (T.base s)))) in ownerFrame-found
 ... | T.forkReadyC rid | true | just f with lookup rid (T.calls (T.front s)) in found |
   P.fresh j rid (T.physical (T.base s)) | P.noParent (P.poolAt w (T.physical (T.base s)))
 ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r in empty | Pool.step (Pool.fork j) (P.poolAt w (T.physical (T.base s)))
 ...     | yes _ | nothing | nothing | just pool = case just-injective eq of λ { refl →
   cong present ownerFrame-found }
 ...     | no _ | _ | _ | _ = case eq of λ ()
 ...     | yes _ | just thread | _ | _ = case eq of λ ()
 ...     | yes _ | nothing | just result | _ = case eq of λ ()
 ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
 fork-safe w j s p eq valid | T.idleC | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.selectedC rid | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.tracingC rid | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.registeringC rid target | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.failedC rid result | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | false | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | true | nothing = case eq of λ ()


 select-safe : ∀ w s p → T.selectPlan w s ≡ just p → Valid s → SafePlan p s
 select-safe w s p eq valid with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
   Monitor.ownerContext w (G.base (T.group (T.base s)))
 ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
   P.muxAt mid (T.physical (T.base s)) | P.noParent (P.poolAt w (T.physical (T.base s))) |
   P.noResults (P.poolAt w (T.physical (T.base s))) | Pool.phase (P.poolAt w (T.physical (T.base s)))
 ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
 ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → tt }
 ...     | Mux.stopping | _ = case eq of λ ()
 ...     | Mux.stopped | _ = case eq of λ ()
 ...     | Mux.failed err | _ = case eq of λ ()
 ...     | Mux.ready | Mux.readActive tr = case eq of λ ()
 ...     | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
 ...     | Mux.ready | Mux.afterStart n = case eq of λ ()
 ...     | Mux.ready | Mux.forkPending n = case eq of λ ()
 ...     | Mux.ready | Mux.afterFailure = case eq of λ ()
 ...     | Mux.ready | Mux.tracerFailed n = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | nothing | _ | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | false | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | false | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closing = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closedPool = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.cancelPending j = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.joinPending j = case eq of λ ()
 select-safe w s p eq valid | false | _ | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | [] | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid (Nat.suc n) ∷ rest | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | false | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | nothing = case eq of λ ()

 register-safe : ∀ j s p → T.registerPlan j s ≡ just p → Valid s → SafePlan p s
 register-safe j s p eq valid with T.byThread j (T.calls (T.front s))
 ... | nothing = case eq of λ ()
 ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
 ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
 ...     | yes _ | yes _ = case just-injective eq of λ { refl → tt }
 ...     | no _ | _ = case eq of λ ()
 ...     | yes _ | no _ = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.idleC = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.selectedC gen = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.tracingC gen = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.forkReadyC gen = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.failedC gen result = case eq of λ ()

 completion-safe : ∀ j result s p → T.completionPlan j result s ≡ just p → Valid s → SafePlan p s
 completion-safe j clean s p eq valid with T.byThread j (T.calls (T.front s)) in found |
   lookup j (P.jobs (T.physical (T.base s)))
 ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
   Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
 ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
   tt }
 ...   | just old | _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
 completion-safe j clean s p eq valid | nothing | _ = case eq of λ ()
 completion-safe j clean s p eq valid | just pair | nothing = case eq of λ ()

 completion-safe j (errored commitErr) s p eq valid with T.byThread j (T.calls (T.front s)) in found |
   lookup j (P.jobs (T.physical (T.base s)))
 ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
   Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
 ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
   tt }
 ...   | just old | _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
 completion-safe j (errored commitErr) s p eq valid | nothing | _ = case eq of λ ()
 completion-safe j (errored commitErr) s p eq valid | just pair | nothing = case eq of λ ()

 poll-safe : ∀ ref w s p → T.pollResultsPlan ref w s ≡ just p → Valid s → SafePlan p s
 poll-safe ref w s p eq valid with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
   lookup ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
   lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
 ... | true | just peer | nothing with Peer.status peer
 ...   | Peer.peerCold = case just-injective eq of λ { refl → tt }
 ...   | Peer.peerCooling = case just-injective eq of λ { refl → tt }
 ...   | Peer.peerWarm with T.firstPeer ref peer s
 ...     | nothing = case eq of λ ()
 ...     | just (kind , result) with T.cleanObservation result
 ...       | true = case just-injective eq of λ { refl → tt }
 ...       | false = case just-injective eq of λ { refl → tt }
 poll-safe ref w s p eq valid | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
 ...     | nothing = case eq of λ ()
 ...     | just (kind , result) with T.cleanObservation result
 ...       | true = case just-injective eq of λ { refl → tt }
 ...       | false = case just-injective eq of λ { refl → tt }
 poll-safe ref w s p eq valid | true | just peer | just f = case just-injective eq of λ { refl → tt }
 poll-safe ref w s p eq valid | false | _ | _ = case eq of λ ()
 poll-safe ref w s p eq valid | true | nothing | _ = case eq of λ ()

 job-wait-safe : ∀ j s p → T.waitJobPlan j s ≡ just p → Valid s → SafePlan p s
 job-wait-safe j s p eq valid with lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s))))
 ... | nothing = case eq of λ ()
 ... | just jf with Sub.queued jf |
   lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
   T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
 ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s
 ...     | nothing = case eq of λ ()
 ...     | just results with T.allClean results
 ...       | true = case just-injective eq of λ { refl → tt }
 ...       | false = case just-injective eq of λ { refl → tt }
 job-wait-safe j s p eq valid | just jf | true | _ | _ = case eq of λ ()
 job-wait-safe j s p eq valid | just jf | false | nothing | _ = case eq of λ ()
 job-wait-safe j s p eq valid | just jf | false | just peer | false = case eq of λ ()

 monitor-wait-safe : ∀ ref s p → T.waitMonitorPlan ref s ≡ just p → Valid s → SafePlan p s
 monitor-wait-safe ref s p eq valid with lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
 ... | nothing = case eq of λ ()
 ... | just f with lookup (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
   T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
 ...   | just peer | true with T.waitResults f peer s
 ...     | nothing = case eq of λ ()
 ...     | just results with T.allClean results
 ...       | true = case just-injective eq of λ { refl → tt }
 ...       | false = case just-injective eq of λ { refl → tt }
 monitor-wait-safe ref s p eq valid | just f | nothing | _ = case eq of λ ()
 monitor-wait-safe ref s p eq valid | just f | just peer | false = case eq of λ ()

 choose-safe : ∀ a s p → T.choose a s ≡ just p → Valid s → SafePlan p s
 choose-safe (T.dispatch a) s p eq valid with T.inheritAllowed a s
 ... | false = case eq of λ ()
 ... | true = case just-injective eq of λ { refl →
   tt }
 choose-safe (T.startNext j rid) s p eq valid with K.peerOpen (T.base s) | T.nextRequest j (T.base s) |
   lookup rid (T.calls (T.front s)) in absent | P.generationFresh rid (P.jobs (T.physical (T.base s)))
 ... | true | just req | nothing | true with canInitiate (Peer.handleRef (T.peer req)) (number (T.protocol req)) |
   P.muxAt (Peer.muxRef (T.peer req)) (T.physical (T.base s))
 ...   | false | _ = case eq of λ ()
 ...   | true | nothing = case eq of λ ()
 ...   | true | just m with Mux.status m
 ...     | Mux.stopping = case eq of λ ()
 ...     | Mux.stopped = case eq of λ ()
 ...     | Mux.failed err = case eq of λ ()
 ...     | Mux.ready with T.slotIdle (T.worker req) (number (T.protocol req)) (T.front s)
 ...       | false = case eq of λ ()
 ...       | true = case just-injective eq of λ { refl → tt }
 choose-safe (T.startNext j rid) s p eq valid | false | _ | _ | _ = case eq of λ ()
 choose-safe (T.startNext j rid) s p eq valid | true | nothing | _ | _ = case eq of λ ()
 choose-safe (T.startNext j rid) s p eq valid | true | just req | just old | _ = case eq of λ ()
 choose-safe (T.startNext j rid) s p eq valid | true | just req | nothing | false = case eq of λ ()
 choose-safe (T.selectStart w) s p eq valid = select-safe w s p eq valid
 choose-safe (T.invokeStartTrace w) s p eq valid with T.cursor w (T.front s) | T.controllerFree w (T.base s)
 ... | T.selectedC rid | true = case just-injective eq of λ { refl → tt }
 choose-safe (T.invokeStartTrace w) s p eq valid | T.idleC | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.tracingC rid | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.forkReadyC rid | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.registeringC rid j | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.failedC rid result | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.selectedC rid | false = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid with T.cursor w (T.front s) | T.controllerFree w (T.base s)
 ... | T.tracingC rid | true = case just-injective eq of λ { refl → tt }
 choose-safe (T.returnStartTrace w) s p eq valid | T.idleC | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.selectedC rid | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.forkReadyC rid | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.registeringC rid j | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.failedC rid result | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.tracingC rid | false = case eq of λ ()
 choose-safe (T.forkStart w j) s p eq valid = fork-safe w j s p eq valid
 choose-safe (T.registerStart j) s p eq valid = register-safe j s p eq valid
 choose-safe (T.commitClean j) s p eq valid = completion-safe j clean s p eq valid
 choose-safe (T.commitError j err) s p eq valid = completion-safe j (errored err) s p eq valid
 choose-safe (T.pollResults ref w) s p eq valid = poll-safe ref w s p eq valid
 choose-safe (T.waitJobResults j) s p eq valid = job-wait-safe j s p eq valid
 choose-safe (T.waitMonitorResults ref) s p eq valid = monitor-wait-safe ref s p eq valid
 choose-safe (T.observeStartTraceException w result) s p eq valid with T.startTraceSelection w result s in selected
 ... | just (rid , fs) = case just-injective eq of λ { refl → trace-selection-safe w result s selected valid }
 ... | nothing = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
   Close.phase (W.shutdown (R.base (N.raw (T.publication (T.base s))))) in awaiting
 ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (R.async err) s in selected
 ...   | just (rid , fs) with W.control Close.acknowledgeDelivery (R.base (N.raw (T.publication (T.base s)))) in received
 ...     | just target = case just-injective eq of λ { refl →
   trace-selection-safe w (R.async err) s selected valid }
 ...     | nothing = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | false | _ = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.initial = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.reading = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.awaitResults = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.closed = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.sendReady entry w = case eq of λ ()
 -- Preservation follows actual enabled event selection, including all guarded
 -- acknowledgments. It assumes no physical registry oracle from callers.
 step-preserves : ∀ a s {t} → T.advance a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with T.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid (choose-safe a s p chosen valid)
 run-preserves : ∀ {s events t} → T.Runs s events t → Valid s → Valid t
 run-preserves T.stop valid = valid
 run-preserves (T.more {s = s} {a = a} actual rest) valid = run-preserves rest (step-preserves a s actual valid)
 initialized-valid : ∀ c g {s} → T.initialize c g ≡ just s → Valid s
 initialized-valid c g eq with K.initial c g in lower
 ... | nothing = case eq of λ ()
 ... | just k = case just-injective eq of λ { refl → Combined.initialized-valid c g lower }
 -- A projected capture gives a real physical thread even after its phases move.
 -- Every initialized frontend run keeps exit phases, mux frames, startup faults
 -- and physical threads in agreement with the shared cleanup records.
 from-initial : ∀ c g {start events s} → T.initialize c g ≡ just start → T.Runs start events s → Valid s
 from-initial c g actual path = run-preserves path (initialized-valid c g actual)
