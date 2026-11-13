{-# OPTIONS --guardedness #-}

-- Every actual mux-prefix writer preserves current-frame negotiated content.
module ConnectionManagement.Properties.LiveTrackerContentMux where

open import Data.Bool using (true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (WorkerId; DecEq-Id)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.HandshakeContinuation as HS
import ConnectionManagement.Domain as HandshakeDomain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.Properties.OutboundHandlerSupervision as Base
import ConnectionManagement.Properties.LiveTrackerChainSteps as Chain
open import ConnectionManagement.Properties.LiveTrackerFrameContent using
 (Content; content; allocation; publication; Covers; at; insert; transport; advance; startup-content; setup-content; publication-writer; published-content)
import Data.Unit
import Data.List.Relation.Unary.All
module Mux where
 private module U = MuxModel Types.TypedResult using (handshakeStep; handshakePending; handshakeFor; captureHandshake; advanceHandshake; Executes; done; next; captured; Action; Frame; module Startup; State; advanceStartup; allocate; allocateHandle; configure; configureMux; registerFor; registerCounters; beforePool; allocationAction; base; baseAllowed; birth; birthFresh; flow; frames; handleAllocated; inherit; initial; negotiate; negotiateReturned; noteBirth; origins; progress; promisePublished; publish; publishSuccess; returnedSuccess; run; setupFor; scheduled; nextSetup; setup; egressSetup; whenSetupDone-just; setFrame; setSource; source; startup; startupAllowed; startupStep; step)
 private module Startup = U.Startup using (observePublication; step)
 Valid : U.State → Set
 Valid s = Covers (U.frames s) (U.source s)
 put-valid : ∀ w f s → Content w f (U.source s) → Valid s → Valid (U.setFrame w f s)
 put-valid w f s present valid = insert w f (U.frames s) (U.source s) present valid
 source-valid : ∀ c s {as} → O.Executes (U.source s) as c → Valid s → Valid (U.setSource c s)
 source-valid c s path valid = transport (U.frames s) path valid
 note-valid : ∀ birth s → Valid s → Valid (U.noteBirth birth s)
 note-valid nothing s valid = valid
 note-valid (just origin) s valid = valid
 inherited : ∀ a s {t} → U.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with U.baseAllowed a s ∧ U.birthFresh (U.birth a (U.base s)) (U.origins s)
 ... | false = case eq of λ ()
 ... | true with B.step a (U.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just b = case just-injective eq of λ { refl → note-valid (U.birth a (U.base s)) (record s { base = b })
   (transport (U.frames s) (proj₂ (Base.machine (Base.step-projects a (U.base s) actual))) valid) }
 negotiated : ∀ w ps flow s {t} → U.negotiateReturned w ps flow s ≡ just t → Valid s → Valid t
 negotiated w ps flow s eq valid with lookup w (B.threads (U.base s)) in found |
   lookup w (U.origins s) | lookup w (U.frames s)
 ... | just thread | just origin | nothing with H.phase thread
 ...   | H.handshaking = case just-injective eq of λ { refl → put-valid w _ s (content Data.Unit.tt Data.Unit.tt) valid }
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
 ...   | H.handshaking = case just-injective eq of λ { refl → put-valid w _ s (content Data.Unit.tt Data.Unit.tt) valid }
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
 ...     | just (next , nothing) = case just-injective eq of λ { refl → put-valid w _ s (content Data.Unit.tt Data.Unit.tt) valid }
 ...     | just (next , just result) with O.advance (O.inbound (Machine.handlerPublication w (HS.asResult result) Machine.resultWritten)) (U.source s) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just c = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s) (content Data.Unit.tt Data.Unit.tt) (source-valid c s (O.next {a = O.inbound (Machine.handlerPublication w (HS.asResult result) Machine.resultWritten)} advanced O.done) valid) }
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
 ...   | U.returnedSuccess with O.advance (O.inbound (Machine.igStep (U.allocationAction f hid mid))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s) (content (Chain.outbound-allocation f hid mid (U.source s) advanced) Data.Unit.tt) (source-valid c s (O.next {a = O.inbound (Machine.igStep (U.allocationAction f hid mid))} advanced O.done) valid) }
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
 ...     | just c = case just-injective eq of λ { refl → λ valid → source-valid c s (O.next {a = O.inbound (Machine.igStep (IG.configureEgress mid (EgressLayout.scheduledLayout slice) limit bound keys))} advanced O.done) valid }
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
 ...     | just c = case just-injective eq of λ { refl → λ valid → source-valid c s (O.next {a = O.inbound (Machine.igStep (IG.registerCells mid))} advanced O.done) valid }
 registered w s eq | just f | U.promisePublished hid mid | false = case eq of λ ()
 registered w s eq | just f | (U.handshakePending helperPC) | _ = case eq of λ ()
 registered w s eq | just f | U.returnedSuccess | _ = case eq of λ ()
 registered w s eq | just f | U.handleAllocated h m | _ = case eq of λ ()

 setup-valid : ∀ w s {t} → U.setupFor w s ≡ just t → Valid s → Valid t
 setup-valid w s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.scheduled f (U.source s) | U.nextSetup (U.setup f)
 ...   | true | just next = case just-injective eq of λ { refl → put-valid w _ s (setup-content w f _ (U.source s) (at (U.frames s) (U.source s) valid w f found)) valid }
 ...   | true | nothing = case eq of λ ()
 ...   | false | _ = case eq of λ ()
 published : ∀ w s {t} → U.publish w s ≡ just t → Valid s → Valid t
 published w s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f in progress
 ...   | U.handleAllocated hid mid with O.advance
   (O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)) (U.source s) in advanced |
   Startup.step Startup.observePublication (U.startup f)
 ...     | just c | just next = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s)
     (published-content w f hid mid next c progress
       (advance (O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)) (U.source s) advanced w f (at (U.frames s) (U.source s) valid w f found))
       (publication-writer w (S.negotiated hid (U.flow f)) (U.source s) advanced))
     (source-valid c s (O.next {a = O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)} advanced O.done) valid) }
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
 ...     | just next = case just-injective eq of λ { refl → put-valid w _ s (startup-content w f _ (U.source s) (at (U.frames s) (U.source s) valid w f found)) valid }
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
 ... | [] | [] | just b = case just-injective eq of λ { refl → Data.List.Relation.Unary.All.[] }
 ... | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | nothing = case eq of λ ()

 -- Induction covers every current frame; no allocation/publication history
 -- oracle or user-supplied registration premise is required.
 run-preserves : ∀ {s events t} → U.Executes s events t → Valid s → Valid t
 run-preserves U.done valid = valid
 run-preserves (U.next {s = s} {a = a} actual rest) valid = run-preserves rest (step-preserves a s actual valid)
 from-initial : ∀ c {start events s} → U.initial c ≡ just start → U.Executes start events s → Valid s
 from-initial c initialized path = run-preserves path (initialized-valid c initialized)
