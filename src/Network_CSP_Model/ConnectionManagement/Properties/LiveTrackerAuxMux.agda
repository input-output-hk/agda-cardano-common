{-# OPTIONS --guardedness #-}

-- The inherited mux-prefix writers preserve auxiliary job/pool references.
-- Protocol metadata is a fixed parameter of this component.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxMux (b : ErrorId → Bool) where
open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; JobId)
open import ConnectionManagement.Store using (Store; lookup)
open import ConnectionManagement.Properties.Entries using (Present)
import ConnectionManagement.Rules.HandshakeContinuation as HS
import ConnectionManagement.Domain as HandshakeDomain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Properties.MuxHandlerSupervision as MuxFacts
import ConnectionManagement.Properties.MuxStartup as StartupFacts
import ConnectionManagement.Properties.LiveTrackerAuxStartup as StartupContent
import ConnectionManagement.Properties.LiveTrackerPoolContent as PoolKernel
open import ConnectionManagement.Properties.LiveTrackerAuxContent b using (Completion; PoolContent)
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
import ConnectionManagement.Properties.LiveTrackerAuxTransport as TransportImport
module Transport = TransportImport b
open Transport using (Retains; by-fields)
module Up = Updates b
module U = P.U
module Startup = P.Startup
module Kernel = PoolKernel Types.TypedResult
module SF = StartupFacts Types.TypedResult
module SC = StartupContent Types.TypedResult
module MF = MuxFacts Types.TypedResult

-- Raw startup child results are refused by MuxProtocolJobs.inheritedAllowed.
Typed : U.Action → Set
Typed a = P.inheritedAllowed a ≡ true
supply : ∀ w a C → Typed (U.startupStep w a) → SC.New a C
supply w (Startup.child action) C ()
supply w Startup.observePublication C allowed = tt
supply w Startup.allocateBuffer C allowed = tt
supply w Startup.createBearer C allowed = tt
supply w Startup.enterRun C allowed = tt
supply w Startup.traceStarting C allowed = tt
supply w Startup.allocateEgress C allowed = tt
supply w Startup.openPool C allowed = tt
supply w (Startup.forkMuxer j) C allowed = tt
supply w Startup.registerMuxer C allowed = tt
supply w (Startup.forkDemuxer j) C allowed = tt
supply w Startup.registerDemuxer C allowed = tt
supply w Startup.traceMature C allowed = tt
supply w Startup.enterMonitor C allowed = tt
supply w (Startup.configureStartup plan) C allowed = tt
supply w (Startup.forkConfigured j) C allowed = tt
supply w Startup.registerConfigured C allowed = tt
supply w Startup.traceConfiguredMature C allowed = tt
supply w Startup.enterConfiguredMonitor C allowed = tt

module For (js : Store JobId Types.ProtocolJob) (pending : Store WorkerId (List JobId))
 (Obs : P.State → Set) (stable : ∀ {s t} → Retains s t → Obs s → Obs t) where
 lift : U.State → P.State
 lift u = P.protocolState u js pending
 Valid : U.State → Set
 Valid u = Up.Valid (lift u) × Obs (lift u)
 same : ∀ s t → U.frames t ≡ U.frames s → (∀ w → P.poolAt w (lift t) ≡ P.poolAt w (lift s)) → Valid s → Valid t
 same s t frames pools (valid , observed) = Up.same-valid (lift s) (lift t) kept frames refl pools valid , stable kept observed
   where
   kept = by-fields (lift s) (lift t) frames (λ w j phase found → phase , subst (λ p → lookup j (P.Pool.handles p) ≡ just phase) (sym (pools w)) found)
     (λ j job found → Types.phase job , found) (λ j w mid dir n gen result found → found)
 source-valid : ∀ c s → Valid s → Valid (U.setSource c s)
 source-valid c s (valid , observed) = Up.source-valid c (lift s) valid , stable (Transport.source c (lift s)) observed
 put-same-startup : ∀ w f next s → lookup w (U.frames s) ≡ just f →
   (∀ hid mid → U.progress f ≡ U.promisePublished hid mid → U.progress next ≡ U.promisePublished hid mid) →
   U.startup next ≡ U.startup f → Valid s → Valid (U.setFrame w next s)
 put-same-startup w f next s found progress sameStartup (valid , observed) = Up.frame-valid w next (lift s) early kept
   (Up.map-pool w (lift s) (lift (U.setFrame w next s)) _ kept (Up.Valid.pools valid w)
     (trans (cong Startup.pool sameStartup) (sym (cong Startup.pool (MF.startup-found w s f found))))) valid , stable kept observed
   where
   early = Up.early-kept f next progress (cong Startup.phase sameStartup) (Up.early-at (Up.Valid.frames valid) w f found)
   kept = Up.frame-retains w f next (lift s) found progress
     (λ role j eq → trans (cong (P.infraId role) (cong Startup.phase sameStartup)) eq)
     (λ j old → subst (λ p → Present j (P.Pool.handles p)) (sym (cong Startup.pool sameStartup)) old)
 put-startup : ∀ w f next s a → lookup w (U.frames s) ≡ just f →
   (∀ hid mid → U.progress f ≡ U.promisePublished hid mid → U.progress next ≡ U.promisePublished hid mid) →
   Up.Early next → (actual : Startup.step a (U.startup f) ≡ just (U.startup next)) →
   (∀ C → SC.New a C) → Valid s → Valid (U.setFrame w next s)
 put-startup w f next s a found progress early actual new (valid , observed) = Up.frame-valid w next (lift s) early kept
   (SC.Evidence.content changed _ (new _) (Up.map-pool w (lift s) (lift (U.setFrame w next s)) _ kept (Up.Valid.pools valid w)
     (sym (cong Startup.pool (MF.startup-found w s f found))))) valid , stable kept observed
   where
   changed = SC.step-evidence a (U.startup f) actual
   kept = Up.frame-retains w f next (lift s) found progress (SC.Evidence.roles changed)
     (Kernel.exec-handles-retained (proj₂ (SF.step-projects a (U.startup f) actual)))
 note-valid : ∀ birth s → Valid s → Valid (U.noteBirth birth s)
 note-valid nothing s valid = valid
 note-valid (just origin) s = same s _ refl (λ w → refl)
 inherited : ∀ a s {t} → U.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with U.baseAllowed a s ∧ U.birthFresh (U.birth a (U.base s)) (U.origins s)
 ... | false = case eq of λ ()
 ... | true with B.step a (U.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just b = case just-injective eq of λ { refl → note-valid (U.birth a (U.base s)) (record s { base = b })
   (same s (record s { base = b }) refl (λ w → refl) valid) }
 negotiated : ∀ w ps flow s {t} → U.negotiateReturned w ps flow s ≡ just t → Valid s → Valid t
 negotiated w ps flow s eq valid with lookup w (B.threads (U.base s)) in found |
   lookup w (U.origins s) | lookup w (U.frames s) in absent
 ... | just thread | just origin | nothing with H.phase thread
 ...   | H.handshaking = case just-injective eq of λ { refl → Up.frame-valid w _ (lift s) refl (Up.fresh-frame w _ (lift s) absent refl) (Kernel.initial _) (proj₁ valid) , stable (Up.fresh-frame w _ (lift s) absent refl) (proj₂ valid) }
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
   lookup w (U.origins s) | lookup w (U.frames s) in absent
 ... | just thread | just origin | nothing with H.phase thread
 ...   | H.handshaking = case just-injective eq of λ { refl → Up.frame-valid w _ (lift s) refl (Up.fresh-frame w _ (lift s) absent refl) (Kernel.initial _) (proj₁ valid) , stable (Up.fresh-frame w _ (lift s) absent refl) (proj₂ valid) }
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
 ...     | just (next , nothing) = case just-injective eq of λ { refl → put-same-startup w f _ s found (λ hid mid published → case trans (sym progress) published of λ ()) refl valid }
 ...     | just (next , just result) with O.advance (O.inbound (Machine.handlerPublication w (HS.asResult result) Machine.resultWritten)) (U.source s) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just c = case just-injective eq of λ { refl → put-same-startup w f _ (U.setSource c s) found (λ hid mid published → case trans (sym progress) published of λ ()) refl (source-valid c s valid) }
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
 ... | just f with U.progress f in progress
 ...   | U.returnedSuccess with O.advance (O.inbound (Machine.igStep (U.allocationAction f hid mid))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → put-same-startup w f _ (U.setSource c s) found
     (λ hid′ mid′ published → case trans (sym progress) published of λ ()) refl (source-valid c s valid) }
 allocated w hid mid s eq valid | just f | (U.handshakePending helperPC) = case eq of λ ()
 allocated w hid mid s eq valid | just f | U.handleAllocated old mid′ = case eq of λ ()
 allocated w hid mid s eq valid | just f | U.promisePublished old mid′ = case eq of λ ()
 -- Configured egress installation writes only the actual allocated mux.
 configured : ∀ w plan limit bound keys s {s′} → U.configure w plan limit bound keys s ≡ just s′ → Valid s → Valid s′
 configured w EgressLayout.plainLayout limit bound keys s eq = case eq of λ ()
 configured w (EgressLayout.scheduledLayout slice) limit bound keys s eq with lookup w (U.frames s)
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f in progress
 ...   | U.handleAllocated hid mid with O.advance (O.inbound (Machine.igStep (IG.configureEgress mid (EgressLayout.scheduledLayout slice) limit bound keys))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → λ valid → source-valid c s valid }
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
 ...     | just c = case just-injective eq of λ { refl → λ valid → source-valid c s valid }
 registered w s eq | just f | U.promisePublished hid mid | false = case eq of λ ()
 registered w s eq | just f | (U.handshakePending helperPC) | _ = case eq of λ ()
 registered w s eq | just f | U.returnedSuccess | _ = case eq of λ ()
 registered w s eq | just f | U.handleAllocated h m | _ = case eq of λ ()

 setup-valid : ∀ w s {t} → U.setupFor w s ≡ just t → Valid s → Valid t
 setup-valid w s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.scheduled f (U.source s) | U.nextSetup (U.setup f)
 ...   | true | just next = case just-injective eq of λ { refl → put-same-startup w f _ s found (λ hid mid published → published) refl valid }
 ...   | true | nothing = case eq of λ ()
 ...   | false | _ = case eq of λ ()
 published : ∀ w s {t} → U.publish w s ≡ just t → Valid s → Valid t
 published w s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f in progress
 ...   | U.handleAllocated hid mid with O.advance
   (O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)) (U.source s) in advanced |
   Startup.step Startup.observePublication (U.startup f) in startupActual
 ...     | just c | just next = case just-injective eq of λ { refl → put-startup w f _ (U.setSource c s)
     Startup.observePublication found (λ hid′ mid′ published → case trans (sym progress) published of λ ()) tt startupActual (λ C → tt) (source-valid c s valid) }
 ...     | nothing | _ = case eq of λ ()
 ...     | just c | nothing = case eq of λ ()
 published w s eq valid | just f | (U.handshakePending helperPC) = case eq of λ ()
 published w s eq valid | just f | U.returnedSuccess = case eq of λ ()
 published w s eq valid | just f | U.promisePublished hid mid = case eq of λ ()
 startup : ∀ w a s {t} → U.advanceStartup w a s ≡ just t → Typed (U.startupStep w a) → Valid s → Valid t
 startup w a s eq allowed valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f in progress | U.startupAllowed a f s
 ...   | U.promisePublished hid mid | true with Startup.step a (U.startup f) in startupActual
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → put-startup w f (record f { startup = next }) s a found (λ hid mid published → published) (Up.early-published _ hid mid progress) startupActual (λ C → supply w a C allowed) valid }
 startup w a s eq allowed valid | just f | (U.handshakePending helperPC) | _ = case eq of λ ()
 startup w a s eq allowed valid | just f | U.returnedSuccess | _ = case eq of λ ()
 startup w a s eq allowed valid | just f | U.handleAllocated hid mid | _ = case eq of λ ()
 startup w a s eq allowed valid | just f | U.promisePublished hid mid | false = case eq of λ ()
 step-preserves : ∀ a s {t} → U.step a s ≡ just t → Typed a → Valid s → Valid t
 step-preserves (U.run a) s eq allowed = inherited a s eq
 step-preserves (U.handshakeStep w event) s eq allowed = handshake-preserves w event s eq
 step-preserves (U.negotiate w ps flow) s eq allowed = negotiated w ps flow s eq
 step-preserves (U.allocateHandle w hid mid) s eq allowed = allocated w hid mid s eq
 step-preserves (U.configureMux w plan limit bound keys) s eq allowed = configured w plan limit bound keys s eq
 step-preserves (U.registerCounters w) s eq allowed = registered w s eq
 step-preserves (U.egressSetup w) s eq allowed = setup-valid w s eq
 step-preserves (U.publishSuccess w) s eq allowed = published w s (U.whenSetupDone-just w s (U.publish w s) eq)
 step-preserves (U.startupStep w a) s eq allowed = startup w a s eq allowed
