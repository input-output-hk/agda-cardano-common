{-# OPTIONS --guardedness #-}

-- Exact descriptor agreement for every stored mux, exit and startup-fault row.
-- All covers traversal rows too, including rows shadowed by duplicate keys.
module ConnectionManagement.Properties.LiveTrackerCaptureLayers where

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
import ConnectionManagement.Rules.HandshakeContinuation as HS
import ConnectionManagement.Domain as HandshakeDomain
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
import ConnectionManagement.MuxStartupUnwind as UnwindModel
open import ConnectionManagement.Properties.LiveTrackerCapture public
import ConnectionManagement.Properties.HandlerAuxBacking as Presence

module Mux where
 private module U = MuxModel Types.TypedResult using (handshakeStep; handshakePending; handshakeFor; captureHandshake; advanceHandshake; captured; Action; Frame; module Startup; State; advanceStartup; allocate; allocateHandle; configure; configureMux; registerFor; registerCounters; beforePool; allocationAction; base; baseAllowed; birth; birthFresh; flow; frames; handleAllocated; inherit; initial; negotiate; negotiateReturned; noteBirth; origins; progress; promisePublished; publish; publishSuccess; returnedSuccess; run; setupFor; scheduled; nextSetup; setup; egressSetup; whenSetupDone-just; setFrame; setSource; source; startup; startupAllowed; startupStep; step)
 private module Startup = U.Startup using (observePublication; step)
 Valid : U.State → Set
 Valid s = Covers (U.frames s) (Birth.MuxLayer.view s)
 put-valid : ∀ w f s → Ref w (U.captured f) (Birth.MuxLayer.view s) → Valid s → Valid (U.setFrame w f s)
 put-valid w f s present valid = covers-put w f (U.frames s) (Birth.MuxLayer.view s) present valid
 source-valid : ∀ c s → Valid s → Valid (U.setSource c s)
 source-valid c s valid = valid
 note-valid : ∀ birth s → Valid s → Valid (U.noteBirth birth s)
 note-valid nothing s valid = valid
 note-valid (just origin) s valid = valid
 inherited : ∀ a s {t} → U.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with U.baseAllowed a s ∧ U.birthFresh (U.birth a (U.base s)) (U.origins s)
 ... | false = case eq of λ ()
 ... | true with B.step a (U.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just b = case just-injective eq of λ { refl → note-valid (U.birth a (U.base s)) (record s { base = b })
   (covers-retained {rows = U.frames s} {before = Birth.physical (U.base s)} {after = Birth.physical b}
     (change-retains (Birth.physical-step-change a (U.base s) actual)) valid) }
 negotiated : ∀ w ps flow s {t} → U.negotiateReturned w ps flow s ≡ just t → Valid s → Valid t
 negotiated w ps flow s eq valid with lookup w (B.threads (U.base s)) in found |
   lookup w (U.origins s) | lookup w (U.frames s)
 ... | just thread | just origin | nothing with H.phase thread
 ...   | H.handshaking = case just-injective eq of λ { refl → put-valid w _ s (physical-present w (U.base s) thread found) valid }
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.maskedSetup = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.caughtCancellation err = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.cancellationPublished err = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.bodyExited err = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.finalizing err = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.cleanupComplete err outcome = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.resultAvailable err outcome = case eq of λ ()
 negotiated w ps flow s eq valid | nothing | origin | old = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | nothing | old = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | just old = case eq of λ ()
 -- Helper frames preserve the same source/capture observation.
 capture-handshake-preserves : ∀ w pc s {t} → U.captureHandshake w pc s ≡ just t → Valid s → Valid t
 capture-handshake-preserves w pc s eq valid with lookup w (B.threads (U.base s)) in found |
   lookup w (U.origins s) | lookup w (U.frames s)
 ... | just thread | just origin | nothing with H.phase thread
 ...   | H.handshaking = case just-injective eq of λ { refl → put-valid w _ s (physical-present w (U.base s) thread found) valid }
 capture-handshake-preserves w pc s eq valid | just thread | just origin | nothing | H.maskedSetup = case eq of λ ()
 capture-handshake-preserves w pc s eq valid | just thread | just origin | nothing | H.caughtCancellation err = case eq of λ ()
 capture-handshake-preserves w pc s eq valid | just thread | just origin | nothing | H.cancellationPublished err = case eq of λ ()
 capture-handshake-preserves w pc s eq valid | just thread | just origin | nothing | H.bodyExited err = case eq of λ ()
 capture-handshake-preserves w pc s eq valid | just thread | just origin | nothing | H.finalizing err = case eq of λ ()
 capture-handshake-preserves w pc s eq valid | just thread | just origin | nothing | H.cleanupComplete err outcome = case eq of λ ()
 capture-handshake-preserves w pc s eq valid | just thread | just origin | nothing | H.resultAvailable err outcome = case eq of λ ()
 capture-handshake-preserves w pc s eq valid | nothing | origin | old = case eq of λ ()
 capture-handshake-preserves w pc s eq valid | just thread | nothing | old = case eq of λ ()
 capture-handshake-preserves w pc s eq valid | just thread | just origin | just old = case eq of λ ()

 -- Metadata stutters; publication executes the actual promise writer.
 advance-handshake-preserves : ∀ w action s {t} → U.advanceHandshake w action s ≡ just t → Valid s → Valid t
 advance-handshake-preserves w action s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f in progress
 ...   | U.handshakePending pc with HS.step action pc
 ...     | just (next , nothing) = case just-injective eq of λ { refl → put-valid w _ s (covers-at valid w f found) valid }
 ...     | just (next , just result) with O.advance (O.inbound (Machine.handlerPublication w (HS.asResult result) Machine.resultWritten)) (U.source s) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just c = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s) (covers-at valid w f found) valid }
 advance-handshake-preserves w action s eq valid | just f | U.handshakePending pc | nothing = case eq of λ ()
 advance-handshake-preserves w action s eq valid | just f | U.returnedSuccess = case eq of λ ()
 advance-handshake-preserves w action s eq valid | just f | U.handleAllocated h mid = case eq of λ ()
 advance-handshake-preserves w action s eq valid | just f | U.promisePublished h mid = case eq of λ ()

 -- Only inbound origins can enter the query delay.
 handshake-preserves : ∀ w event s {t} → U.handshakeFor w event s ≡ just t → Valid s → Valid t
 handshake-preserves w (HS.limitReturned kind err) s eq valid = capture-handshake-preserves w (HS.returned (HS.protocolLimit kind err)) s eq valid
 handshake-preserves w (HS.bearerTimedOut err) s eq valid = capture-handshake-preserves w (HS.returned (HS.bearerTimeout err)) s eq valid
 handshake-preserves w HS.queryReturned s eq valid with lookup w (U.origins s)
 ... | just HandshakeDomain.inbound = capture-handshake-preserves w (HS.returned HS.query) s eq valid
 ... | just HandshakeDomain.outbound = case eq of λ ()
 ... | nothing = case eq of λ ()
 handshake-preserves w (HS.continue action) s eq valid = advance-handshake-preserves w action s eq valid

 allocated : ∀ w hid mid s {t} → U.allocate w hid mid s ≡ just t → Valid s → Valid t
 allocated w hid mid s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.returnedSuccess with O.advance (O.inbound (Machine.igStep (U.allocationAction f hid mid))) (U.source s)
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s) (covers-at valid w f found) valid }
 allocated w hid mid s eq valid | just f | (U.handshakePending helperPC) = case eq of λ ()
 allocated w hid mid s eq valid | just f | U.handleAllocated old mid′ = case eq of λ ()
 allocated w hid mid s eq valid | just f | U.promisePublished old mid′ = case eq of λ ()
 -- Configured egress installation writes only the actual allocated mux.
 configured : ∀ w plan limit bound keys s {s′} → U.configure w plan limit bound keys s ≡ just s′ → Valid s → Valid s′
 configured w EgressLayout.plainLayout limit bound keys s eq = case eq of λ ()
 configured w (EgressLayout.scheduledLayout slice) limit bound keys s eq with lookup w (U.frames s)
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance (O.inbound (Machine.igStep (IG.configureEgress mid (EgressLayout.scheduledLayout slice) limit bound keys))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → λ valid → valid }
 configured w (EgressLayout.scheduledLayout slice) limit bound keys s eq | just f | (U.handshakePending helperPC) = case eq of λ ()
 configured w (EgressLayout.scheduledLayout slice) limit bound keys s eq | just f | U.returnedSuccess = case eq of λ ()
 configured w (EgressLayout.scheduledLayout slice) limit bound keys s eq | just f | U.promisePublished h m = case eq of λ ()

 -- Counter registration writes only the actual IG registry.
 registered : ∀ w s {s′} → U.registerFor w s ≡ just s′ → Valid s → Valid s′
 registered w s eq with lookup w (U.frames s)
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | U.beforePool (U.Startup.phase (U.startup f))
 ...   | U.promisePublished hid mid | true with O.advance (O.inbound (Machine.igStep (IG.registerCells mid))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → λ valid → valid }
 registered w s eq | just f | U.promisePublished hid mid | false = case eq of λ ()
 registered w s eq | just f | (U.handshakePending helperPC) | _ = case eq of λ ()
 registered w s eq | just f | U.returnedSuccess | _ = case eq of λ ()
 registered w s eq | just f | U.handleAllocated h m | _ = case eq of λ ()

 setup-valid : ∀ w s {t} → U.setupFor w s ≡ just t → Valid s → Valid t
 setup-valid w s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.scheduled f (U.source s) | U.nextSetup (U.setup f)
 ...   | true | just next = case just-injective eq of λ { refl → put-valid w _ s (covers-at valid w f found) valid }
 ...   | true | nothing = case eq of λ ()
 ...   | false | _ = case eq of λ ()
 published : ∀ w s {t} → U.publish w s ≡ just t → Valid s → Valid t
 published w s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance
   (O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)) (U.source s) |
   Startup.step Startup.observePublication (U.startup f)
 ...     | just c | just next = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s) (covers-at valid w f found) valid }
 ...     | nothing | _ = case eq of λ ()
 ...     | just c | nothing = case eq of λ ()
 published w s eq valid | just f | (U.handshakePending helperPC) = case eq of λ ()
 published w s eq valid | just f | U.returnedSuccess = case eq of λ ()
 published w s eq valid | just f | U.promisePublished hid mid = case eq of λ ()
 startup : ∀ w a s {t} → U.advanceStartup w a s ≡ just t → Valid s → Valid t
 startup w a s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | U.startupAllowed a f s
 ...   | U.promisePublished hid mid | true with Startup.step a (U.startup f)
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → put-valid w _ s (covers-at valid w f found) valid }
 startup w a s eq valid | just f | (U.handshakePending helperPC) | allowed = case eq of λ ()
 startup w a s eq valid | just f | U.returnedSuccess | allowed = case eq of λ ()
 startup w a s eq valid | just f | U.handleAllocated hid mid | allowed = case eq of λ ()
 startup w a s eq valid | just f | U.promisePublished hid mid | false = case eq of λ ()
 step-preserves : ∀ a s {t} → U.step a s ≡ just t → Valid s → Valid t
 step-preserves (U.run a) = inherited a
 step-preserves (U.handshakeStep w event) = handshake-preserves w event
 step-preserves (U.negotiate w ps flow) = negotiated w ps flow
 step-preserves (U.allocateHandle w hid mid) = allocated w hid mid
 step-preserves (U.configureMux w plan limit bound keys) s eq = configured w plan limit bound keys s eq
 step-preserves (U.registerCounters w) s eq = registered w s eq
 step-preserves (U.egressSetup w) = setup-valid w
 step-preserves (U.publishSuccess w) s eq = published w s (U.whenSetupDone-just w s (U.publish w s) eq)
 step-preserves (U.startupStep w a) = startup w a
 initialized-valid : ∀ c {s} → U.initial c ≡ just s → Valid s
 initialized-valid c eq with IG.handles (IG.execution (Machine.inboundGovernor (O.core c))) |
   IG.muxes (IG.execution (Machine.inboundGovernor (O.core c))) | B.initial c
 ... | [] | [] | just b = case just-injective eq of λ { refl → covers-empty {U.Frame} (Birth.physical b) }
 ... | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | nothing = case eq of λ ()

 open Presence.Mux public using (coordinator; IsDirect; direct-shutdown-same)

import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolProperties
import ConnectionManagement.Rules.MuxRuntime as WireMux
module Protocol where
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; Action; module Pool; module Startup; State; module U; appendPending; asyncInfraResult; asyncProtocolResult; base; commitClean; control; controlReady; deregisterInfra; deregisterProtocol; forkInitiator; forkResponder; infraId; infrastructureReturn; inherit; inheritedAllowed; initial; jobs; monitorControl; monitoring; muxAt; noParent; poolAt; protocolException; protocolReturned; unlessAwaiting-just; publishInfra; publishProtocol; register; registerProtocol; removePublished; returnProtocol; returned; run; setPool; setSource; source; sourceControl; step; viaInfra; viaProtocol; viaDb; viaDb-source; submitDb-via; awaitDb-via; dbFailure-via; DbFailure; refused; abandoned; submitDbWrite; awaitDbWrite; dbWriteFailed; writerComplete; writerSeal)
 private module U = P.U using (handshakeStep; handshakePending; handshakeFor; captureHandshake; advanceHandshake; captured; base; frames; handleAllocated; initial; progress; promisePublished; returnedSuccess; startup; step)
 private module Pool = P.Pool using (bodyReturnedWith; deregister; parentFork; publishAsyncResult; publishCompletion; register; step)
 private module Startup = P.Startup using (phase)
 private module Old = ProtocolProperties using (EgressChange; enter-observation; send-observation; muxer-egress-observation; BodyReturn; CompletionCommit; Fork; Publication; clean-observation; exception-observation; initiator-fork-observation; publication-observation; responder-fork-observation; return-observation)
 Valid : P.State → Set
 Valid s = Mux.Valid (P.base s)
 source-valid : ∀ c s → Valid s → Valid (P.setSource c s)
 source-valid c s valid = valid
 pool-valid : ∀ w f p s → Ref w (P.U.captured f) (Birth.ProtocolLayer.view s) → Valid s → Valid (P.setPool w f p s)
 pool-valid w f p s present valid = Mux.put-valid w _ (P.base s) present valid
 pending-valid : ∀ job j s → Valid s → Valid (P.appendPending job j s)
 pending-valid job j s valid with Types.direction job
 ... | WireMux.initiatorJob = valid
 ... | WireMux.responderJob = valid
 removed-valid : ∀ job kept s → Valid s → Valid (P.removePublished job kept s)
 removed-valid job kept s valid with Types.direction job
 ... | WireMux.initiatorJob = valid
 ... | WireMux.responderJob = valid
 inherited : ∀ a s {t} → P.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with P.inheritedAllowed a
 ... | false = case eq of λ ()
 ... | true with U.step a (P.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just u = case just-injective eq of λ { refl → Mux.step-preserves a (P.base s) actual valid }
 fork-valid : ∀ w j gen s {t} → Old.Fork w j gen s t → Valid s → Valid t
 fork-valid w j gen s observation valid rewrite Old.Fork.after-shape observation =
   pool-valid w (Old.Fork.ownerFrame observation) (Old.Fork.poolAfter observation)
     (P.setSource (Old.Fork.sourceAfter observation) s)
     (covers-at valid w (Old.Fork.ownerFrame observation) (Old.Fork.frame-before observation)) valid
 commit-valid : ∀ j s {t} → Old.CompletionCommit j s t → Valid s → Valid t
 commit-valid j s observation valid rewrite Old.CompletionCommit.after-shape observation =
   pending-valid (Old.CompletionCommit.capturedJob observation) j _ valid
 body-valid : ∀ j s {t} → Old.BodyReturn j s t → Valid s → Valid t
 body-valid j s observation valid rewrite Old.BodyReturn.after-shape observation =
   pool-valid (Types.owner (Old.BodyReturn.capturedJob observation))
     (Old.BodyReturn.ownerFrame observation) (Old.BodyReturn.poolAfter observation) s
     (covers-at valid _ _ (Old.BodyReturn.frame-before observation)) valid
 publication-valid : ∀ j s {t} → Old.Publication j s t → Valid s → Valid t
 publication-valid j s observation valid rewrite Old.Publication.after-shape observation =
   removed-valid (Old.Publication.capturedJob observation) (Old.Publication.remainingPending observation) _
     (pool-valid (Types.owner (Old.Publication.capturedJob observation))
       (Old.Publication.ownerFrame observation) (Old.Publication.poolAfter observation)
       (P.setSource (Old.Publication.sourceAfter observation) s)
       (covers-at valid _ _ (Old.Publication.frame-before observation)) valid)
 returned : ∀ j s {t} → P.returned j s ≡ just t → Valid s → Valid t
 returned j s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with Types.phase job
 ...   | Types.executing with P.hasWanton j job s
 ...     | false = case eq of λ ()
 ...     | true = case just-injective eq of λ { refl → valid }
 returned j s eq valid | just job | Types.waitingEgress = case eq of λ ()
 returned j s eq valid | just job | Types.resultCaptured result = case eq of λ ()
 registered : ∀ j s {t} → P.register j s ≡ just t → Valid s → Valid t
 registered j s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) in found | Pool.parentFork (P.poolAt (Types.owner job) s)
 ...   | just f | just current with j ≟ current
 ...     | no _ = case eq of λ ()
 ...     | yes _ with Pool.step Pool.register (P.poolAt (Types.owner job) s)
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f p s (covers-at valid _ _ found) valid }
 registered j s eq valid | just job | nothing | _ = case eq of λ ()
 registered j s eq valid | just job | just f | nothing = case eq of λ ()
 via-protocol : ∀ j a s {t} → P.viaProtocol j a s ≡ just t → Valid s → Valid t
 via-protocol j a s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) in found | Pool.step a (P.poolAt (Types.owner job) s)
 ...   | just f | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f p s (covers-at valid _ _ found) valid }
 ...   | nothing | _ = case eq of λ ()
 ...   | just f | nothing = case eq of λ ()
 via-infra : ∀ w role a s {t} → P.viaInfra w role a s ≡ just t → Valid s → Valid t
 via-infra w role a s eq valid with lookup w (U.frames (P.base s)) in found
 ... | nothing = case eq of λ ()
 ... | just f with P.infraId role (Startup.phase (U.startup f))
 ...   | nothing = case eq of λ ()
 ...   | just j with Pool.step (a j) (P.poolAt w s)
 ...     | nothing = case eq of λ ()
 ...     | just p = case just-injective eq of λ { refl → pool-valid w f p s (covers-at valid _ _ found) valid }
 control : ∀ w a s {t} → P.monitorControl w a s ≡ just t → Valid s → Valid t
 control w a s eq valid with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | P.monitoring f | P.noParent (P.poolAt w s)
 ...   | U.promisePublished hid mid | true | true with P.muxAt mid s
 ...     | nothing = case eq of λ ()
 ...     | just m with P.controlReady a m (P.poolAt w s)
 ...       | false = case eq of λ ()
 ...       | true with O.advance (O.inbound (Machine.igStep (P.sourceControl a mid))) (P.source s)
 ...         | nothing = case eq of λ ()
 ...         | just c = case just-injective eq of λ { refl → valid }
 control w a s eq valid | just f | (U.handshakePending helperPC) | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.returnedSuccess | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.handleAllocated hid mid | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | false | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | true | false = case eq of λ ()
 -- Source egress changes do not replace any captured owner frame.
 egress-valid : ∀ s {t} → Old.EgressChange s t → Valid s → Valid t
 egress-valid s observation valid rewrite Old.EgressChange.after-shape observation = valid
 -- DB queue/await steps change only the source configuration.
 db-valid : ∀ a s {t} → P.viaDb a s ≡ just t → Valid s → Valid t
 db-valid a s eq valid with P.viaDb-source a s eq
 ... | c , advanced , refl = valid
 step-preserves : ∀ a s {t} → P.step a s ≡ just t → Valid s → Valid t
 step-preserves (P.run a) = inherited a
 step-preserves (P.forkResponder w j gen) s eq = fork-valid w j gen s (Old.responder-fork-observation w j gen s eq)
 step-preserves (P.forkInitiator w j gen n) s eq = fork-valid w j gen s (Old.initiator-fork-observation w j gen n s eq)
 step-preserves (P.registerProtocol j) = registered j
 step-preserves (P.enterProtocolBody j) s eq = egress-valid s (Old.enter-observation j s eq)
 step-preserves (P.appendProtocolPayload j bytes) s eq = egress-valid s (Old.send-observation j bytes s eq)
 step-preserves (P.egressMuxer w action) s eq = egress-valid s (Old.muxer-egress-observation w action s eq)
 step-preserves (P.protocolReturned j) s eq = returned j s (P.unlessAwaiting-just j s _ eq)
 step-preserves (P.commitClean j) s eq = commit-valid j s (Old.clean-observation j s eq)
 step-preserves (P.protocolException j err) s eq = commit-valid j s (Old.exception-observation j err s eq)
 step-preserves (P.returnProtocol j) s eq = body-valid j s (Old.return-observation j s eq)
 step-preserves (P.publishProtocol j) s eq = publication-valid j s (Old.publication-observation j s eq)
 step-preserves (P.deregisterProtocol j) = via-protocol j (Pool.deregister j)
 step-preserves (P.asyncProtocolResult j) = via-protocol j (Pool.publishAsyncResult j)
 step-preserves (P.infrastructureReturn w role err) = via-infra w role (λ j → Pool.bodyReturnedWith j (Types.infraResult role err))
 step-preserves (P.publishInfra w role) = via-infra w role Pool.publishCompletion
 step-preserves (P.deregisterInfra w role) = via-infra w role Pool.deregister
 step-preserves (P.asyncInfraResult w role) = via-infra w role Pool.publishAsyncResult
 step-preserves (P.control w a) = control w a
 step-preserves (P.submitDbWrite j d) s eq = db-valid _ s (P.submitDb-via j d s eq)
 step-preserves (P.awaitDbWrite j) s eq = db-valid _ s (P.awaitDb-via j s eq)
 step-preserves (P.writerComplete d) s eq = db-valid _ s eq
 step-preserves (P.writerSeal err) s eq = db-valid _ s eq
 step-preserves (P.dbWriteFailed j) s eq valid with P.dbFailure-via j s eq
 ... | P.refused err failed = commit-valid j s (Old.exception-observation j err s failed) valid
 ... | P.abandoned err mid abandon failed = commit-valid j mid (Old.exception-observation j err mid failed) (db-valid _ s abandon valid)
 initialized-valid : ∀ c {s} → P.initial c ≡ just s → Valid s
 initialized-valid c eq with U.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just u = case just-injective eq of λ { refl → Mux.initialized-valid c actual }

 open Presence.Protocol public using (coordinator; IsDirect; direct-shutdown-same)

import ConnectionManagement.MuxResultMonitor as MonitorModel
open import ConnectionManagement.IGTypes using (clean; errored)
open import Relation.Nullary using (does)
module Monitor (isBearerClosed : ErrorId → Bool) where
 private module W = MonitorModel isBearerClosed using (Action; State; base; beginDead; commitTracer; consume; deadAction; deadReady; deadTracing; delegateAllowed; demuxFinish; failed; findCaptured; finishDead; finishMatches; finishMux; finishProtocol; finishProtocolTrace; finished; handleHead; handleProtocol; handleSelected; inherit; initial; initiatorTracing; legacyMatches; muxAt; ownerContext; pcAt; poolAt; protocolSource; recordFinish; responderTracing; run; sampleTracer; selectHead; selected; setPC; setSource; source; startDead; statusAction; step; traceSource; tracing; viaSource; waiting)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; initial; jobs; monitoring; noParent; step)
 private module U = P.U using (handshakeStep; handshakePending; handshakeFor; captureHandshake; advanceHandshake; captured; base; frames; handleAllocated; progress; promisePublished; returnedSuccess)
 private module Pool = P.Pool using (completions; consumeCompletion; step)
 Valid : W.State → Set
 Valid s = Protocol.Valid (W.base s)
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s valid = valid
 coordinator : W.State → Close.State
 coordinator s = B.shutdown (U.base (P.base (W.base s)))
 record CIPaths (before after : W.State) : Set where
  constructor paths
  field preserves : Valid before → Valid after
        same-shutdown : coordinator after ≡ coordinator before
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths (λ valid → valid) refl
 ci-pc-paths : ∀ w pc s → CIPaths s (W.setPC w pc s)
 ci-pc-paths w pc s = paths (λ valid → valid) refl
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose first second = paths (λ valid → CIPaths.preserves second (CIPaths.preserves first valid)) (trans (CIPaths.same-shutdown second) (CIPaths.same-shutdown first))
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s eq = paths (λ valid → valid) refl
 inherited : ∀ a s {t} → W.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with P.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → Protocol.step-preserves a (W.base s) actual valid }
 owner-present : ∀ w s {f mid} → W.ownerContext w s ≡ just (f , mid) → Valid s → Ref w (P.U.captured f) (Birth.MonitorLayer.view isBearerClosed s)
 owner-present w s eq valid with lookup w (U.frames (P.base (W.base s))) in found
 ... | nothing = case eq of λ ()
 ... | just actual with U.progress actual | P.monitoring actual
 ...   | U.promisePublished hid mid | true = case just-injective eq of λ { refl → covers-at valid w actual found }
 ...   | U.promisePublished hid mid | false = case eq of λ ()
 ...   | (U.handshakePending helperPC) | _ = case eq of λ ()
 ...   | U.returnedSuccess | _ = case eq of λ ()
 ...   | U.handleAllocated hid mid | _ = case eq of λ ()
 ci-via-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-select-projects : ∀ w s {s′} → W.selectHead w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.pcAt w s | W.ownerContext w s in context
 ... | W.waiting | just (f , mid) with W.muxAt mid s | P.noParent (W.poolAt w s) | Pool.completions (W.poolAt w s)
 ...   | just m | true | item ∷ rest with WireMux.status m | WireMux.callback m
 ...     | WireMux.ready | WireMux.returned with Pool.step Pool.consumeCompletion (W.poolAt w s) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → paths (λ valid → Protocol.pool-valid w f next (W.base s) (owner-present w s context valid) valid) refl }
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.stopping | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.stopped | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.failed err | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.readActive tr = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.commitTrace active tr = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.afterStart n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.forkPending n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.afterFailure = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.tracerFailed n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | nothing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just _ | false | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just _ | true | [] = case eq of λ ()
 ci-select-projects w s eq | W.waiting | nothing = case eq of λ ()
 ci-select-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-select-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.finished outcome | _ = case eq of λ ()

 ci-pc-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPC w pc after)
 ci-pc-after w pc {after = after} path = ci-compose path (ci-pc-paths w pc after)
 ci-protocol-source-projects : ∀ w mid dir n outcome s {s′} → W.protocolSource w mid dir n outcome s ≡ just s′ → CIPaths s s′
 ci-protocol-source-projects w mid WireMux.responderJob n outcome s eq with W.muxAt mid s
 ... | nothing = case eq of λ ()
 ... | just m with W.legacyMatches n outcome (WireMux.completions m)
 ...   | false = case eq of λ ()
 ...   | true with W.viaSource (IG.monitorCompletion mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-pc-after w (W.responderTracing outcome) (ci-via-projects (IG.monitorCompletion mid) s advanced) }
 ci-protocol-source-projects w mid WireMux.initiatorJob n clean s eq = case just-injective eq of λ { refl → ci-pc-paths w (W.initiatorTracing clean) s }
 ci-protocol-source-projects w mid WireMux.initiatorJob n (errored err) s eq with W.viaSource (IG.recordMuxFailure mid err) s in advanced
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → ci-pc-after w (W.initiatorTracing (errored err)) (ci-via-projects (IG.recordMuxFailure mid err) s advanced) }
 ci-handle-protocol-projects : ∀ w dir n gen outcome s {s′} → W.handleProtocol w dir n gen outcome s ≡ just s′ → CIPaths s s′
 ci-handle-protocol-projects w dir n gen outcome s eq with W.ownerContext w s | W.findCaptured w dir n gen outcome (P.jobs (W.base s))
 ... | just (f , mid) | just (j , job) with does (Types.mux job ≟ mid) | W.muxAt mid s
 ...   | true | just m with WireMux.status m | WireMux.callback m
 ...     | WireMux.ready | WireMux.returned = ci-protocol-source-projects w mid dir n outcome s eq
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.stopping | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.stopped | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.failed err | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.readActive tr = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.commitTrace active tr = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.afterStart k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.forkPending k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.afterFailure = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.tracerFailed k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | false | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | nothing = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | nothing | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just _ | nothing = case eq of λ ()
 ci-record-finish-projects : ∀ w outcome s {s′} → W.recordFinish w outcome s ≡ just s′ → CIPaths s s′
 ci-record-finish-projects w outcome s eq with W.ownerContext w s
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with W.viaSource (W.statusAction outcome mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadReady outcome) (ci-via-projects (W.statusAction outcome mid) s advanced) }
 ci-handle-projects : ∀ w s {s′} → W.handleHead w s ≡ just s′ → CIPaths s s′
 ci-handle-projects w s eq with W.pcAt w s
 ... | W.selected (Types.protocolCompletion dir n gen outcome) = ci-handle-protocol-projects w dir n gen outcome s eq
 ... | W.selected (Types.infraMuxer err) = ci-record-finish-projects w (W.failed err) s eq
 ... | W.selected (Types.infraDemuxer err) = ci-record-finish-projects w (W.demuxFinish w err s) s eq
 ... | W.waiting = case eq of λ ()
 ... | W.responderTracing _ = case eq of λ ()
 ... | W.initiatorTracing _ = case eq of λ ()
 ... | W.deadReady _ = case eq of λ ()
 ... | W.deadTracing _ = case eq of λ ()
 ... | W.finished _ = case eq of λ ()
 ci-trace-projects : ∀ sample w s {s′} → W.traceSource sample w s ≡ just s′ → CIPaths s s′
 ci-trace-projects sample w s eq with W.tracing (W.pcAt w s) | W.ownerContext w s
 ... | true | just (f , mid) with sample
 ...   | true = ci-via-projects (IG.sampleTracer mid) s eq
 ...   | false = ci-via-projects (IG.commitTracer mid) s eq
 ci-trace-projects sample w s eq | false | _ = case eq of λ ()
 ci-trace-projects sample w s eq | true | nothing = case eq of λ ()
 ci-finish-protocol-projects : ∀ w s {s′} → W.finishProtocol w s ≡ just s′ → CIPaths s s′
 ci-finish-protocol-projects w s eq with W.pcAt w s | W.ownerContext w s
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s }
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.afterFailure = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s }
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.returned = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s }
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s }
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing result | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.finished outcome | _ = case eq of λ ()

 ci-start-dead-projects : ∀ w s {s′} → W.startDead w s ≡ just s′ → CIPaths s s′
 ci-start-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
 ... | W.deadReady outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with W.finishMatches outcome (WireMux.status m) | W.deadAction outcome (WireMux.callback m) mid
 ...     | true | just action with W.viaSource action s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadTracing outcome) (ci-via-projects action s advanced) }
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | false | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | true | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()
 ci-finish-dead-projects : ∀ w s {s′} → W.finishMux w s ≡ just s′ → CIPaths s s′
 ci-finish-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
 ... | W.deadTracing outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with WireMux.callback m | W.finishMatches outcome (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → ci-pc-paths w (W.finished outcome) s }
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.readActive tr | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.afterStart n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.forkPending n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.afterFailure | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.returned | false = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | nothing = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | nothing = case eq of λ ()
 ci-finish-dead-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()

 step-preserves : ∀ action s {s′} → W.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (W.run action) s eq = inherited action s eq
 step-preserves (W.consume w) s eq = CIPaths.preserves (ci-select-projects w s eq)
 step-preserves (W.handleSelected w) s eq = CIPaths.preserves (ci-handle-projects w s eq)
 step-preserves (W.sampleTracer w) s eq = CIPaths.preserves (ci-trace-projects true w s eq)
 step-preserves (W.commitTracer w) s eq = CIPaths.preserves (ci-trace-projects false w s eq)
 step-preserves (W.finishProtocolTrace w) s eq = CIPaths.preserves (ci-finish-protocol-projects w s eq)
 step-preserves (W.beginDead w) s eq = CIPaths.preserves (ci-start-dead-projects w s eq)
 step-preserves (W.finishDead w) s eq = CIPaths.preserves (ci-finish-dead-projects w s eq)
 open Presence.Monitor isBearerClosed public using (IsDirect; direct-shutdown-same)
 initialized-valid : ∀ c {s} → W.initial c ≡ just s → Valid s
 initialized-valid c eq with P.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → Protocol.initialized-valid c actual }

import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.Properties.MuxGroupShutdown as GroupProperties
import Data.Nat as Nat
module Group (isBearerClosed : ErrorId → Bool) where
 private module W = GroupModel isBearerClosed using (Action; module M; State; abortMonitor; abortOwner; abortStage; asyncDead; asyncDeadTracing; asyncExit; asyncFailure; asyncFailureWritten; asyncTrace; base; beginAsyncDead; beginWhole; beginWholeClose; cancelPC; captureGroup; captureMini; childEligible; commitAsyncTracer; commitStoppedTracer; delegateAllowed; deliverGroup; deliverMini; deliverWhole; deliverWholeChild; delivered; discardClean; drainEmpty; drainReady; draining; failedExit; findOwner; finishAsync; finishAsyncDead; finishChildUnwind; finishGroup; finishMini; finishNormalScope; finishOrdinary; finishStopped; finishStoppedTrace; finishWhole; finishWholeClose; frameAt; fromPhase; groupClosing; idle; inherit; initial; isInfra; joinGroup; joinMini; joinMiniHead; joinWhole; joined; miniMember; monitorReturnedNormal; normalExit; observeStoppingTrace; observeTraceStopped; ownerAborting; ownerContext; ownerOf; phase; poolAt; prepareUnwind; protocolState; ready; registeredMini; remaining; replaceUnwind; replacementEligible; requestGroup; requestGroupCancel; requestShutdown; requestStop; retireFor; retireAllowed; retireCounters; requestWholeCancel; requested; run; sameStage; sampleAsyncTracer; sampleStoppedTracer; scopeDone; selectShutdown; selectStop; setFrame; setPhase; setPool; setProtocols; setSource; shutdownSelected; source; sourcePhase; step; stoppedTrace; stoppedTracing; stoppingTraced; stoppingWritten; timeout2Elapsed; unwindChild; unwindReplacedBySync; viaPool; viaSource; wholeAction; wholeClosed; wholeClosing; wholeDeliverable; wholeOutcome; writeAsyncFailure; writeStopped; writeStopping)
 private module M = W.M using (deadReady; deadTracing; failed; finishMatches; finished; initial; initiatorTracing; pcAt; responderTracing; selected; step; waiting)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; jobs; locate; muxAt; noParent; noResults; pendingAt; protocolException; sameOutcome; step)
 private module U = P.U using (handshakeStep; handshakePending; handshakeFor; captureHandshake; advanceHandshake; captured; module Startup; frames; handleAllocated; progress; promisePublished; returnedSuccess; startup)
 private module Startup = U.Startup using (pool)
 private module Pool = P.Pool using (beginClose; bodyReturned; bodyRunning; bodyUnwinding; bodyUnwound; cancelPending; closedPool; closing; deliverCancel; deregisterPending; deregistered; finishClose; handles; interruptJob; join; joinPending; openPool; phase; requestCancel; resultAvailable; resumeAfterUnwindError; sameSnapshot; step)
 private module Lower = Monitor isBearerClosed using (Valid; coordinator; initialized-valid; owner-present; step-preserves)
 open W using (remaining; joined; cancelPC)
 Valid : W.State → Set
 Valid s = Lower.Valid (W.base s)
 coordinator : W.State → Close.State
 coordinator s = Lower.coordinator (W.base s)
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s valid = valid
 record CIPaths (before after : W.State) : Set where
  constructor paths
  field preserves : Valid before → Valid after
        same-shutdown : coordinator after ≡ coordinator before
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths (λ valid → valid) refl
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose first second = paths (λ valid → CIPaths.preserves second (CIPaths.preserves first valid))
   (trans (CIPaths.same-shutdown second) (CIPaths.same-shutdown first))
 ci-frame-paths : ∀ w f s → CIPaths s (W.setFrame w f s)
 ci-frame-paths w f s = paths (λ valid → valid) refl
 ci-phase-paths : ∀ w pc s → CIPaths s (W.setPhase w pc s)
 ci-phase-paths w pc s = ci-frame-paths w _ s
 ci-phase-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPhase w pc after)
 ci-phase-after w pc {after = after} path = ci-compose path (ci-phase-paths w pc after)
 ci-frame-after : ∀ w f {before after} → CIPaths before after → CIPaths before (W.setFrame w f after)
 ci-frame-after w f {after = after} path = ci-compose path (ci-frame-paths w f after)
 ci-protocol-projects : ∀ s p → (Protocol.Valid (W.protocolState s) → Protocol.Valid p) →
   Protocol.coordinator p ≡ Protocol.coordinator (W.protocolState s) → CIPaths s (W.setProtocols p s)
 ci-protocol-projects s p proof same = paths proof same
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s eq = paths (λ valid → valid) refl
 inherited : ∀ a s {t} → W.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with M.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just m = case just-injective eq of λ { refl → Lower.step-preserves a (W.base s) actual valid }
 owner-present : ∀ w s {f mid} → W.ownerContext w s ≡ just (f , mid) → Valid s → Ref w (P.U.captured f) (Birth.GroupLayer.view isBearerClosed s)
 owner-present w s found = Lower.owner-present w (W.base s) found
 find-present : ∀ j rows {w f registry} → W.findOwner j rows ≡ just (w , f) → Covers rows registry → Ref w (P.U.captured f) registry
 find-present j [] () valid
 find-present j ((q , first) ∷ rows) {registry = registry} eq valid with lookup j (Pool.handles (Startup.pool (U.startup first)))
 ... | just result = case just-injective eq of λ { refl → covers-at valid q first (lookup-head q first rows) }
 ... | nothing = find-present j rows {registry = registry} eq (covers-tail q first rows registry valid)
 ownerOf-present : ∀ j s {w f} → W.ownerOf j s ≡ just (w , f) → Valid s → Ref w (P.U.captured f) (Birth.GroupLayer.view isBearerClosed s)
 ownerOf-present j s eq valid = find-present j (U.frames (P.base (W.protocolState s))) {registry = Birth.GroupLayer.view isBearerClosed s} eq valid
 ci-via-source-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-source-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-pool-step : ∀ w f action s {p} → Pool.step action (W.poolAt w s) ≡ just p →
   (Valid s → Ref w (P.U.captured f) (Birth.GroupLayer.view isBearerClosed s)) → CIPaths s (W.setPool w f p s)
 ci-pool-step w f action s {p} eq present = paths (λ valid → Protocol.pool-valid w f p (W.protocolState s) (present valid) valid) refl
 ci-via-pool-projects : ∀ w action s {s′} → W.viaPool w action s ≡ just s′ → CIPaths s s′
 ci-via-pool-projects w action s eq with W.ownerContext w s in context
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with Pool.step action (W.poolAt w s) in advanced
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → ci-pool-step w f action s advanced (owner-present w s context) }
 ci-from-phase-projects : ∀ w before after s {s′} → W.fromPhase w before after s ≡ just s′ → CIPaths s s′
 ci-from-phase-projects w before after s eq with W.sameStage before (W.phase (W.frameAt w s))
 ... | false = case eq of λ ()
 ... | true = case just-injective eq of λ { refl → ci-phase-paths w after s }
 ci-source-phase-projects : ∀ w before after action s {s′} → W.sourcePhase w before after action s ≡ just s′ → CIPaths s s′
 ci-source-phase-projects w before after action s eq with W.sameStage before (W.phase (W.frameAt w s)) | W.ownerContext w s
 ... | true | just (f , mid) with W.viaSource (action mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w after (ci-via-source-projects (action mid) s advanced) }
 ci-source-phase-projects w before after action s eq | false | _ = case eq of λ ()
 ci-source-phase-projects w before after action s eq | true | nothing = case eq of λ ()
 ci-request-projects : ∀ w s {s′} → W.requestStop w s ≡ just s′ → CIPaths s s′
 ci-request-projects w s eq with lookup w (U.frames (P.base (W.protocolState s)))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.promisePublished hid mid = ci-via-source-projects (IG.enqueueMuxStop mid) s eq
 ...   | (U.handshakePending helperPC) = case eq of λ ()
 ...   | U.returnedSuccess = case eq of λ ()
 ...   | U.handleAllocated hid mid = case eq of λ ()
 -- Counter retirement writes only the actual IG registry at scopeDone.
 ci-retire-projects : ∀ w s {s′} → W.retireFor w s ≡ just s′ → CIPaths s s′
 ci-retire-projects w s eq with W.retireAllowed (W.phase (W.frameAt w s))
 ... | false = case eq of λ ()
 ... | true with lookup w (U.frames (P.base (W.protocolState s)))
 ...   | nothing = case eq of λ ()
 ...   | just f with U.progress f
 ...     | U.promisePublished hid mid = ci-via-source-projects (IG.retireCells mid) s eq
 ...     | (U.handshakePending helperPC) = case eq of λ ()
 ...     | U.returnedSuccess = case eq of λ ()
 ...     | U.handleAllocated hid mid = case eq of λ ()
 ci-select-projects : ∀ w s {s′} → W.selectStop w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.phase (W.frameAt w s) | M.pcAt w (W.base s) | W.ownerContext w s
 ... | W.idle | M.waiting | just (f , mid) with P.noParent (W.poolAt w s) | P.noResults (W.poolAt w s)
 ...   | true | true with W.viaSource (IG.takeShutdownCommand mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-phase-after w W.shutdownSelected (ci-via-source-projects (IG.takeShutdownCommand mid) s advanced) }
 ci-select-projects w s eq | W.idle | M.waiting | just (f , mid) | false | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.waiting | just (f , mid) | true | false = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.waiting | nothing = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.selected item | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.responderTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.initiatorTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.deadReady outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.deadTracing outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.finished outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-capture-projects : ∀ w order s {s′} → W.captureMini w order s ≡ just s′ → CIPaths s s′
 ci-capture-projects w order s eq with W.phase (W.frameAt w s) | Pool.sameSnapshot order (W.registeredMini w s) | P.noParent (W.poolAt w s)
 ... | W.stoppingWritten | true | true = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ... | W.stoppingWritten | false | _ = case eq of λ ()
 ... | W.stoppingWritten | true | false = case eq of λ ()
 ci-capture-projects w order s eq | W.idle | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.draining | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-request-group-projects : ∀ w s {s′} → W.requestGroup w s ≡ just s′ → CIPaths s s′
 ci-request-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.ready | j ∷ rest = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ... | W.groupClosing | W.ready | [] = case eq of λ ()
 ... | W.groupClosing | W.requested j | _ = case eq of λ ()
 ... | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects : ∀ w s {s′} → W.deliverMini w s ≡ just s′ → CIPaths s s′
 ci-deliver-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.requested j | current ∷ rest with j ≟ current | W.miniMember w j s | W.childEligible j s
 ...   | yes same | true | true with W.viaPool w (Pool.interruptJob j) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-frame-after w _ (ci-via-pool-projects w (Pool.interruptJob j) s advanced) }
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | no apart | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | false | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | true | false = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | [] = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.ready | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-join-head-projects : ∀ w current s {s′} → W.joinMiniHead w current s ≡ just s′ → CIPaths s s′
 ci-join-head-projects w current s eq with W.remaining (W.frameAt w s) | lookup current (Pool.handles (W.poolAt w s))
 ... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
 ...   | yes same = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ...   | no apart = case eq of λ ()
 ci-join-head-projects w current s eq | [] | _ = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | nothing = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.bodyReturned result) = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.deregisterPending exit) = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.deregistered exit) = case eq of λ ()
 ci-join-group-projects : ∀ w s {s′} → W.joinMini w s ≡ just s′ → CIPaths s s′
 ci-join-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s)
 ... | W.groupClosing | W.requested j = ci-join-head-projects w j s eq
 ... | W.groupClosing | W.delivered j = ci-join-head-projects w j s eq
 ... | W.groupClosing | W.ready = case eq of λ ()
 ci-join-group-projects w s eq | W.idle | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.draining | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-group-projects : ∀ w s {s′} → W.finishMini w s ≡ just s′ → CIPaths s s′
 ci-finish-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.ready | [] = case just-injective eq of λ { refl → ci-phase-paths w W.draining s }
 ... | W.groupClosing | W.ready | _ ∷ _ = case eq of λ ()
 ... | W.groupClosing | W.requested j | _ = case eq of λ ()
 ... | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-discard-projects : ∀ j job s {s′} → W.discardClean j job s ≡ just s′ → CIPaths s s′
 ci-discard-projects j job s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → ci-idle s }
 ... | WireMux.responderJob with P.locate j (P.pendingAt (Types.owner job) (W.protocolState s)) | P.muxAt (Types.mux job) (W.protocolState s)
 ...   | just (index , kept) | just m with IG.takePending index (WireMux.finishedJobs m)
 ...     | just ((n , result) , rest) with does (n Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome ConnectionManagement.IGTypes.clean result
 ...       | true with W.viaSource (IG.discardJobOccurrence (Types.mux job) index) s in advanced
 ...         | nothing = case eq of λ ()
 ...         | just next = case just-injective eq of λ { refl → ci-compose
   (ci-via-source-projects (IG.discardJobOccurrence (Types.mux job) index) s advanced)
   (ci-protocol-projects next _ (λ valid → valid) refl) }
 ci-discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | nothing = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | nothing | _ = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | just pair | nothing = case eq of λ ()
 ci-prepare-projects : ∀ j w f s {s′} → W.prepareUnwind j w f s ≡ just s′ → CIPaths s s′
 ci-prepare-projects j w f s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing with W.isInfra j f
 ...   | true = case just-injective eq of λ { refl → ci-idle s }
 ...   | false = case eq of λ ()
 ci-prepare-projects j w f s eq | just job with does (w ≟ Types.owner job) | Types.phase job
 ... | true | Types.executing = case just-injective eq of λ { refl → ci-idle s }
 ... | true | Types.waitingEgress = case just-injective eq of λ { refl → ci-idle s }
 ... | true | Types.resultCaptured ConnectionManagement.IGTypes.clean = ci-discard-projects j job s eq
 ... | true | Types.resultCaptured (ConnectionManagement.IGTypes.errored err) = case eq of λ ()
 ... | false | _ = case eq of λ ()
 ci-unwind-projects : ∀ j s {s′} → W.unwindChild j s ≡ just s′ → CIPaths s s′
 ci-unwind-projects j s eq with W.ownerOf j s in owned
 ... | nothing = case eq of λ ()
 ... | just (w , f) with lookup j (Pool.handles (W.poolAt w s))
 ...   | just Pool.bodyUnwinding with W.prepareUnwind j w f s in prepared
 ...     | nothing = case eq of λ ()
 ...     | just next with Pool.step (Pool.bodyUnwound j) (W.poolAt w next) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → paths
   (λ valid → Protocol.pool-valid w f p (W.protocolState next)
     (subst (Ref w (P.U.captured f)) (sym (Birth.GroupLayer.CIPaths.retention (Birth.GroupLayer.ci-prepare-projects isBearerClosed j w f s prepared)))
       (ownerOf-present j s owned valid))
     (CIPaths.preserves (ci-prepare-projects j w f s prepared) valid))
   (CIPaths.same-shutdown (ci-prepare-projects j w f s prepared)) }
 ci-unwind-projects j s eq | just (w , f) | nothing = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just Pool.bodyRunning = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.bodyReturned result) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.deregisterPending exit) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.deregistered exit) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.resultAvailable exit) = case eq of λ ()
 ci-replacement-projects : ∀ j err s {s′} → W.replaceUnwind j err s ≡ just s′ → CIPaths s s′
 ci-replacement-projects j err s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing = case eq of λ ()
 ... | just job with W.replacementEligible (Types.phase job) | W.ownerOf j s in owned
 ...   | true | just (w , f) with does (w ≟ Types.owner job) | Pool.step (Pool.resumeAfterUnwindError j) (W.poolAt w s) in advanced
 ...     | true | just p with P.step (P.protocolException j err) (W.protocolState (W.setPool w f p s)) in captured
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-compose
   (ci-pool-step w f (Pool.resumeAfterUnwindError j) s advanced (ownerOf-present j s owned))
   (ci-protocol-projects (W.setPool w f p s) next
     (Protocol.step-preserves (P.protocolException j err) (W.protocolState (W.setPool w f p s)) captured)
     (Protocol.direct-shutdown-same (P.protocolException j err) (W.protocolState (W.setPool w f p s)) captured tt)) }
 ci-replacement-projects j err s eq | just job | true | just (w , f) | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq | just job | true | just (w , f) | true | nothing = case eq of λ ()
 ci-replacement-projects j err s eq | just job | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq | just job | true | nothing = case eq of λ ()
 ci-abort-projects : ∀ w err s {s′} → W.abortMonitor w err s ≡ just s′ → CIPaths s s′
 ci-abort-projects w err s eq with W.abortStage w s | W.ownerContext w s | P.noParent (W.poolAt w s)
 ... | true | just (f , mid) | true with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m
 ...     | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w (W.ownerAborting err) s }
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.readActive tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.afterStart n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.forkPending n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.afterFailure = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | nothing = case eq of λ ()
 ci-abort-projects w err s eq | false | _ | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | nothing | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | just pair | false = case eq of λ ()
 ci-begin-whole-projects : ∀ w order s {s′} → W.beginWhole w order s ≡ just s′ → CIPaths s s′
 ci-begin-whole-projects w order s eq with W.wholeOutcome w s
 ... | nothing = case eq of λ ()
 ... | just outcome with W.viaPool w (Pool.beginClose order) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosing outcome) (ci-via-pool-projects w (Pool.beginClose order) s advanced) }
 ci-whole-action-projects : ∀ w action s {s′} → W.wholeAction w action s ≡ just s′ → CIPaths s s′
 ci-whole-action-projects w action s eq with W.phase (W.frameAt w s)
 ... | W.wholeClosing outcome = ci-via-pool-projects w action s eq
 ci-whole-action-projects w action s eq | W.idle = case eq of λ ()
 ci-whole-action-projects w action s eq | W.shutdownSelected = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppingTraced = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppingWritten = case eq of λ ()
 ci-whole-action-projects w action s eq | W.groupClosing = case eq of λ ()
 ci-whole-action-projects w action s eq | W.draining = case eq of λ ()
 ci-whole-action-projects w action s eq | W.drainReady = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppedTrace = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppedTracing = case eq of λ ()
 ci-whole-action-projects w action s eq | W.monitorReturnedNormal = case eq of λ ()
 ci-whole-action-projects w action s eq | W.ownerAborting err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.wholeClosed outcome = case eq of λ ()
 ci-whole-action-projects w action s eq | W.asyncFailureWritten err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.asyncDeadTracing err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.scopeDone outcome = case eq of λ ()
 ci-whole-delivery-projects : ∀ w s {s′} → W.deliverWholeChild w s ≡ just s′ → CIPaths s s′
 ci-whole-delivery-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
 ... | W.wholeClosing outcome | just (f , mid) | Pool.cancelPending j with W.wholeDeliverable w j f s
 ...   | true = ci-via-pool-projects w Pool.deliverCancel s eq
 ...   | false = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | nothing | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.openPool = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closing = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closedPool = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.joinPending j = case eq of λ ()
 ci-finish-whole-projects : ∀ w s {s′} → W.finishWhole w s ≡ just s′ → CIPaths s s′
 ci-finish-whole-projects w s eq with W.phase (W.frameAt w s)
 ... | W.wholeClosing outcome with W.viaPool w Pool.finishClose s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosed outcome) (ci-via-pool-projects w Pool.finishClose s advanced) }
 ci-finish-whole-projects w s eq | W.idle = case eq of λ ()
 ci-finish-whole-projects w s eq | W.shutdownSelected = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppingTraced = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppingWritten = case eq of λ ()
 ci-finish-whole-projects w s eq | W.groupClosing = case eq of λ ()
 ci-finish-whole-projects w s eq | W.draining = case eq of λ ()
 ci-finish-whole-projects w s eq | W.drainReady = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppedTrace = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppedTracing = case eq of λ ()
 ci-finish-whole-projects w s eq | W.monitorReturnedNormal = case eq of λ ()
 ci-finish-whole-projects w s eq | W.ownerAborting err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.wholeClosed outcome = case eq of λ ()
 ci-finish-whole-projects w s eq | W.asyncFailureWritten err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.asyncDeadTracing err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.scopeDone outcome = case eq of λ ()
 ci-async-failure-projects : ∀ w s {s′} → W.asyncFailure w s ≡ just s′ → CIPaths s s′
 ci-async-failure-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s) | W.ownerContext w s
 ... | W.wholeClosed (W.asyncExit err) | Pool.closedPool | just (f , mid) with W.viaSource (IG.recordAsyncMuxFailure mid err) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncFailureWritten err) (ci-via-source-projects (IG.recordAsyncMuxFailure mid err) s advanced) }
 ci-async-failure-projects w s eq | W.wholeClosed W.normalExit | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.failedExit err) | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closedPool | nothing = case eq of λ ()
 ci-async-failure-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.openPool | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closing | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.cancelPending j | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.joinPending j | _ = case eq of λ ()
 ci-async-dead-projects : ∀ w s {s′} → W.asyncDead w s ≡ just s′ → CIPaths s s′
 ci-async-dead-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
 ... | W.asyncFailureWritten err | just (f , mid) with W.viaSource (IG.traceMuxDead mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncDeadTracing err) (ci-via-source-projects (IG.traceMuxDead mid) s advanced) }
 ci-async-dead-projects w s eq | W.asyncFailureWritten err | nothing = case eq of λ ()
 ci-async-dead-projects w s eq | W.idle | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.groupClosing | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.draining | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-async-trace-projects : ∀ sample w s {s′} → W.asyncTrace sample w s ≡ just s′ → CIPaths s s′
 ci-async-trace-projects sample w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
 ... | W.asyncDeadTracing err | just (f , mid) with sample
 ...   | true = ci-via-source-projects (IG.sampleTracer mid) s eq
 ...   | false = ci-via-source-projects (IG.commitTracer mid) s eq
 ci-async-trace-projects sample w s eq | W.asyncDeadTracing err | nothing = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.idle | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.groupClosing | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.draining | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.drainReady | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-async-projects : ∀ w s {s′} → W.finishAsync w s ≡ just s′ → CIPaths s s′
 ci-finish-async-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
 ... | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m | M.finishMatches (M.failed err) (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.asyncExit err)) s }
 ...     | WireMux.returned | false = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.readActive tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.afterStart n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.forkPending n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.afterFailure | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | nothing = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | nothing | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.openPool = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closing = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.cancelPending j = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.joinPending j = case eq of λ ()
 ci-finish-ordinary-projects : ∀ w s {s′} → W.finishOrdinary w s ≡ just s′ → CIPaths s s′
 ci-finish-ordinary-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s)
 ... | W.wholeClosed W.normalExit | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone W.normalExit) s }
 ... | W.wholeClosed (W.failedExit err) | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.failedExit err)) s }
 ... | W.wholeClosed (W.asyncExit err) | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.idle | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.groupClosing | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.draining | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.openPool = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.closing = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.cancelPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.joinPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.openPool = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.closing = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.cancelPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.joinPending j = case eq of λ ()
 ci-finish-stopped-projects : ∀ w s {s′} → W.finishStopped w s ≡ just s′ → CIPaths s s′
 ci-finish-stopped-projects w s eq with W.sameStage W.stoppedTracing (W.phase (W.frameAt w s)) | W.ownerContext w s
 ... | true | just (f , mid) with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.status m | WireMux.callback m
 ...     | WireMux.stopped | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w W.monitorReturnedNormal s }
 ...     | WireMux.stopped | WireMux.readActive tr = case eq of λ ()
 ...     | WireMux.stopped | WireMux.commitTrace flag tr = case eq of λ ()
 ...     | WireMux.stopped | WireMux.afterStart n = case eq of λ ()
 ...     | WireMux.stopped | WireMux.forkPending n = case eq of λ ()
 ...     | WireMux.stopped | WireMux.afterFailure = case eq of λ ()
 ...     | WireMux.stopped | WireMux.tracerFailed n = case eq of λ ()
 ...     | WireMux.ready | _ = case eq of λ ()
 ...     | WireMux.stopping | _ = case eq of λ ()
 ...     | WireMux.failed err | _ = case eq of λ ()
 ci-finish-stopped-projects w s eq | true | just (f , mid) | nothing = case eq of λ ()
 ci-finish-stopped-projects w s eq | false | _ = case eq of λ ()
 ci-finish-stopped-projects w s eq | true | nothing = case eq of λ ()

 step-preserves : ∀ action s {s′} → W.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (W.run action) s eq = inherited action s eq
 step-preserves (W.requestShutdown w) s eq = CIPaths.preserves (ci-request-projects w s eq)
 step-preserves (W.retireCounters w) s eq = CIPaths.preserves (ci-retire-projects w s eq)
 step-preserves (W.selectShutdown w) s eq = CIPaths.preserves (ci-select-projects w s eq)
 step-preserves (W.observeStoppingTrace w) s eq = CIPaths.preserves (ci-from-phase-projects w W.shutdownSelected W.stoppingTraced s eq)
 step-preserves (W.writeStopping w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppingTraced W.stoppingWritten IG.recordMuxStopping s eq)
 step-preserves (W.captureGroup w order) s eq = CIPaths.preserves (ci-capture-projects w order s eq)
 step-preserves (W.requestGroupCancel w) s eq = CIPaths.preserves (ci-request-group-projects w s eq)
 step-preserves (W.deliverGroup w) s eq = CIPaths.preserves (ci-deliver-group-projects w s eq)
 step-preserves (W.joinGroup w) s eq = CIPaths.preserves (ci-join-group-projects w s eq)
 step-preserves (W.finishGroup w) s eq = CIPaths.preserves (ci-finish-group-projects w s eq)
 step-preserves (W.drainEmpty w) s eq = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s (GroupProperties.drain-phase isBearerClosed w s eq))
 step-preserves (W.timeout2Elapsed w) s eq = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s eq)
 step-preserves (W.writeStopped w) s eq = CIPaths.preserves (ci-source-phase-projects w W.drainReady W.stoppedTrace IG.completeMuxStopping s eq)
 step-preserves (W.observeTraceStopped w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTrace W.stoppedTracing IG.traceGracefulMuxStopped s eq)
 step-preserves (W.sampleStoppedTracer w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.sampleTracer s eq)
 step-preserves (W.commitStoppedTracer w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.commitTracer s eq)
 step-preserves (W.finishStoppedTrace w) s eq = CIPaths.preserves (ci-finish-stopped-projects w s eq)
 step-preserves (W.finishChildUnwind j) s eq = CIPaths.preserves (ci-unwind-projects j s eq)
 step-preserves (W.unwindReplacedBySync j err) s eq = CIPaths.preserves (ci-replacement-projects j err s eq)
 step-preserves (W.abortOwner w err) s eq = CIPaths.preserves (ci-abort-projects w err s eq)
 step-preserves (W.beginWholeClose w order) s eq = CIPaths.preserves (ci-begin-whole-projects w order s eq)
 step-preserves (W.requestWholeCancel w) s eq = CIPaths.preserves (ci-whole-action-projects w Pool.requestCancel s eq)
 step-preserves (W.deliverWhole w) s eq = CIPaths.preserves (ci-whole-delivery-projects w s eq)
 step-preserves (W.joinWhole w) s eq = CIPaths.preserves (ci-whole-action-projects w Pool.join s eq)
 step-preserves (W.finishWholeClose w) s eq = CIPaths.preserves (ci-finish-whole-projects w s eq)
 step-preserves (W.finishNormalScope w) s eq = CIPaths.preserves (ci-finish-ordinary-projects w s eq)
 step-preserves (W.writeAsyncFailure w) s eq = CIPaths.preserves (ci-async-failure-projects w s eq)
 step-preserves (W.beginAsyncDead w) s eq = CIPaths.preserves (ci-async-dead-projects w s eq)
 step-preserves (W.sampleAsyncTracer w) s eq = CIPaths.preserves (ci-async-trace-projects true w s eq)
 step-preserves (W.commitAsyncTracer w) s eq = CIPaths.preserves (ci-async-trace-projects false w s eq)
 step-preserves (W.finishAsyncDead w) s eq = CIPaths.preserves (ci-finish-async-projects w s eq)
 open Presence.Group isBearerClosed public using (IsDirect; direct-shutdown-same)
 initialized-valid : ∀ c {s} → W.initial c ≡ just s → Valid s
 initialized-valid c eq with M.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just m = case just-injective eq of λ { refl → Lower.initialized-valid c actual }


