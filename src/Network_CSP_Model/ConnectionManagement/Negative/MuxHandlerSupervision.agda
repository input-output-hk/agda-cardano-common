{-# OPTIONS --guardedness #-}

-- Coupled successful-handler startup at the fixed source pin. Actual physical
-- births precede negotiation/allocation/publication; the prefix ends at monitor
-- entry, with no pool-close, buffer-unwind or full-shutdown claim.
module ConnectionManagement.Negative.MuxHandlerSupervision where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (Protocol)
open import ConnectionManagement.Store using (Store; put; lookup)
import ConnectionManagement.MuxHandlerSupervision as Coupled
module U = Coupled ⊤
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as M
import ConnectionManagement.State as Shared
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.MuxStartup as StartupRules
module S = StartupRules ⊤
module Pool = S.Pool
import ConnectionManagement.Negative.MuxStartup as Stages
import ConnectionManagement.Negative.OutboundHandlerSupervision as Prior
import ConnectionManagement.CSP.OutboundAdmission as Fixture
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (key₀; key₁; w₁; child₁; r₁)

ps : List Protocol
ps = G.proto ∷ []
born : Store WorkerId Provenance
born = (Fixture.child , outbound) ∷ []
wrap : B.State → Store WorkerId Provenance → U.State
wrap b history = U.supervised b history []
q₀ : U.State
q₀ = wrap Prior.p₀ []
actual-initializer : U.initial (O.initial F.start) ≡ just q₀
actual-initializer = refl
q1 : U.State
q1 = wrap Prior.p1 []
q2 : U.State
q2 = wrap Prior.p2 []
q3 : U.State
q3 = wrap Prior.p3 []
q4 : U.State
q4 = wrap Prior.p4 []
q5 : U.State
q5 = wrap Prior.p5 []
q6 : U.State
q6 = wrap Prior.p6 []
q7 : U.State
q7 = wrap Prior.p7 []
q8 : U.State
q8 = wrap Prior.p8 []
q9 : U.State
q9 = wrap Prior.p9 []
q10 : U.State
q10 = wrap Prior.p10 born
q11 : U.State
q11 = wrap Prior.p11 born
q12 : U.State
q12 = wrap Prior.p12 born
birth-step1 : U.step (U.run (B.outbound (O.beginAcquire Fixture.caller Fixture.req))) q₀ ≡ just q1
birth-step1 = refl
birth-step2 : U.step (U.run (B.outbound (O.acquire Fixture.caller (A.select nothing)))) q1 ≡ just q2
birth-step2 = refl
birth-step3 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.readCounters))) q2 ≡ just q3
birth-step3 = refl
birth-step4 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.newPromise))) q3 ≡ just q4
birth-step4 = refl
birth-step5 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.openOK))) q4 ≡ just q5
birth-step5 = refl
birth-step6 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.configureOK))) q5 ≡ just q6
birth-step6 = refl
birth-step7 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.connectOK))) q6 ≡ just q7
birth-step7 = refl
birth-step8 : U.step (U.run (B.outbound (O.acquire Fixture.caller (A.gotLocal (local key₀))))) q7 ≡ just q8
birth-step8 = refl
birth-step9 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.updateLocalAddress))) q8 ≡ just q9
birth-step9 = refl
birth-step10 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.forkOK))) q9 ≡ just q10
birth-step10 = refl
birth-step11 : U.step (U.run (B.handler (H.enterHandshake Fixture.child))) q10 ≡ just q11
birth-step11 = refl
birth-step12 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.commitConnected))) q11 ≡ just q12
birth-step12 = refl
birthActions : List U.Action
birthActions = (U.run (B.outbound (O.beginAcquire Fixture.caller Fixture.req))) ∷ (U.run (B.outbound (O.acquire Fixture.caller (A.select nothing)))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.readCounters))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.newPromise))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.openOK))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.configureOK))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.connectOK))) ∷ (U.run (B.outbound (O.acquire Fixture.caller (A.gotLocal (local key₀))))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.updateLocalAddress))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.forkOK))) ∷ (U.run (B.handler (H.enterHandshake Fixture.child))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.commitConnected))) ∷ []
abstract
  initialized-birth : U.Executes q₀ birthActions q12
  initialized-birth = U.next birth-step1 (U.next birth-step2 (U.next birth-step3 (U.next birth-step4 (U.next birth-step5 (U.next birth-step6 (U.next birth-step7 (U.next birth-step8 (U.next birth-step9 (U.next birth-step10 (U.next birth-step11 (U.next birth-step12 (U.done))))))))))))

returnedFrame allocatedFrame : U.Frame
returnedFrame = U.frame Prior.captured outbound ps duplex U.returnedSuccess S.initial
allocatedFrame = U.frame Prior.captured outbound ps duplex (U.handleAllocated (ident 0) (ident 0)) S.initial
publishedFrame : S.State → U.Frame
publishedFrame stage = U.frame Prior.captured outbound ps duplex (U.promisePublished (ident 0) (ident 0)) stage
allocatedBase publishedBase : B.State
allocatedBase = record Prior.p12 { source = Fixture.withHandle Prior.connectedSource }
publishedBase = record Prior.p12 { source = Fixture.withHandle (Fixture.at (A.count Fixture.wait) Fixture.published) }
q13 q14 q15 : U.State
q13 = U.supervised Prior.p12 born ((Fixture.child , returnedFrame) ∷ [])
q14 = U.supervised allocatedBase born ((Fixture.child , allocatedFrame) ∷ [])
q15 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₁) ∷ [])
actual-negotiate : U.step (U.negotiate Fixture.child ps duplex) q12 ≡ just q13
actual-negotiate = refl
actual-handle-allocation : U.step (U.allocateHandle Fixture.child (ident 0) (ident 0)) q13 ≡ just q14
actual-handle-allocation = refl
actual-coupled-publication : U.step (U.publishSuccess Fixture.child) q14 ≡ just q15
actual-coupled-publication = refl
success-promise-visible-before-buffer : lookup (ident 0) (Shared.handshakeResults (M.world (O.core (U.source q15)))) ≡ just (Shared.negotiated (ident 0) duplex)
success-promise-visible-before-buffer = refl
publication-has-no-physical-jobs : Pool.handles (S.pool (U.startupAt Fixture.child q15)) ≡ []
publication-has-no-physical-jobs = refl
publication-startup-phase : S.phase (U.startupAt Fixture.child q15) ≡ S.published
publication-startup-phase = refl
q16 : U.State
q16 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₂) ∷ [])
startup-step16 : U.step (U.startupStep Fixture.child (S.allocateBuffer)) q15 ≡ just q16
startup-step16 = refl
q17 : U.State
q17 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₃) ∷ [])
startup-step17 : U.step (U.startupStep Fixture.child (S.createBearer)) q16 ≡ just q17
startup-step17 = refl
q18 : U.State
q18 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₄) ∷ [])
startup-step18 : U.step (U.startupStep Fixture.child (S.enterRun)) q17 ≡ just q18
startup-step18 = refl
q19 : U.State
q19 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₅) ∷ [])
startup-step19 : U.step (U.startupStep Fixture.child (S.traceStarting)) q18 ≡ just q19
startup-step19 = refl
q20 : U.State
q20 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₆) ∷ [])
startup-step20 : U.step (U.startupStep Fixture.child (S.allocateEgress)) q19 ≡ just q20
startup-step20 = refl
q21 : U.State
q21 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₇) ∷ [])
startup-step21 : U.step (U.startupStep Fixture.child (S.openPool)) q20 ≡ just q21
startup-step21 = refl
q22 : U.State
q22 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₈) ∷ [])
startup-step22 : U.step (U.startupStep Fixture.child (S.forkMuxer (ident 0))) q21 ≡ just q22
startup-step22 = refl
q23 : U.State
q23 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₉) ∷ [])
startup-step23 : U.step (U.startupStep Fixture.child (S.registerMuxer)) q22 ≡ just q23
startup-step23 = refl
q24 : U.State
q24 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₁₀) ∷ [])
startup-step24 : U.step (U.startupStep Fixture.child (S.forkDemuxer (ident 1))) q23 ≡ just q24
startup-step24 = refl
q25 : U.State
q25 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₁₁) ∷ [])
startup-step25 : U.step (U.startupStep Fixture.child (S.registerDemuxer)) q24 ≡ just q25
startup-step25 = refl
q26 : U.State
q26 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₁₂) ∷ [])
startup-step26 : U.step (U.startupStep Fixture.child (S.traceMature)) q25 ≡ just q26
startup-step26 = refl
q27 : U.State
q27 = U.supervised publishedBase born ((Fixture.child , publishedFrame Stages.s₁₃) ∷ [])
startup-step27 : U.step (U.startupStep Fixture.child (S.enterMonitor)) q26 ≡ just q27
startup-step27 = refl
startupActions : List U.Action
startupActions = U.negotiate Fixture.child ps duplex ∷ U.allocateHandle Fixture.child (ident 0) (ident 0) ∷ U.publishSuccess Fixture.child ∷ (U.startupStep Fixture.child (S.allocateBuffer)) ∷ (U.startupStep Fixture.child (S.createBearer)) ∷ (U.startupStep Fixture.child (S.enterRun)) ∷ (U.startupStep Fixture.child (S.traceStarting)) ∷ (U.startupStep Fixture.child (S.allocateEgress)) ∷ (U.startupStep Fixture.child (S.openPool)) ∷ (U.startupStep Fixture.child (S.forkMuxer (ident 0))) ∷ (U.startupStep Fixture.child (S.registerMuxer)) ∷ (U.startupStep Fixture.child (S.forkDemuxer (ident 1))) ∷ (U.startupStep Fixture.child (S.registerDemuxer)) ∷ (U.startupStep Fixture.child (S.traceMature)) ∷ (U.startupStep Fixture.child (S.enterMonitor)) ∷ []
startup-path : U.Executes q12 startupActions q27
startup-path = U.next actual-negotiate (U.next actual-handle-allocation (U.next actual-coupled-publication (U.next startup-step16 (U.next startup-step17 (U.next startup-step18 (U.next startup-step19 (U.next startup-step20 (U.next startup-step21 (U.next startup-step22 (U.next startup-step23 (U.next startup-step24 (U.next startup-step25 (U.next startup-step26 (U.next startup-step27 (U.done)))))))))))))))
append : ∀ {s as t bs u} → U.Executes s as t → U.Executes t bs u → U.Executes s (as ++ bs) u
append U.done right = right
append (U.next eq left) right = U.next eq (append left right)
abstract
  initialized-monitor-entry : U.Executes q₀ (birthActions ++ startupActions) q27
  initialized-monitor-entry = append initialized-birth startup-path
same-pool-contains-both-registered-engines : Pool.registered (S.pool (U.startupAt Fixture.child q27)) ≡ (ident 1) ∷ (ident 0) ∷ []
same-pool-contains-both-registered-engines = refl
no-separate-publication-observation : U.step (U.startupStep Fixture.child S.observePublication) q14 ≡ nothing
no-separate-publication-observation = refl
no-publication-before-allocation : U.step (U.publishSuccess Fixture.child) q13 ≡ nothing
no-publication-before-allocation = refl
no-buffer-before-publication : U.step (U.startupStep Fixture.child S.allocateBuffer) q14 ≡ nothing
no-buffer-before-publication = refl
no-old-handshake-cancel-after-negotiate : U.step (U.run (B.handler (H.deliverHandshakeCancellation Fixture.child (errorId 9)))) q13 ≡ nothing
no-old-handshake-cancel-after-negotiate = refl
no-old-handshake-cancel-after-publish : U.step (U.run (B.handler (H.deliverHandshakeCancellation Fixture.child (errorId 9)))) q15 ≡ nothing
no-old-handshake-cancel-after-publish = refl
no-old-body-exit-shortcut : U.step (U.run (B.handler (H.enterFinalizer Fixture.child))) q15 ≡ nothing
no-old-body-exit-shortcut = refl
no-old-physical-result-shortcut : U.step (U.run (B.handler (H.publishAsyncResult Fixture.child))) q27 ≡ nothing
no-old-physical-result-shortcut = refl
no-raw-lifecycle-shortcut : U.step (U.run (B.handler (H.run (M.handlerStep Fixture.child Life.finishBuffer)))) q27 ≡ nothing
no-raw-lifecycle-shortcut = refl
no-raw-publication : U.step (U.run (B.handler (H.run (M.handlerPublication Fixture.child (Shared.negotiated (ident 0) duplex) M.resultWritten)))) q14 ≡ nothing
no-raw-publication = refl
no-raw-handle-allocation : U.step (U.run (B.handler (H.run (M.igStep (IG.installOutboundHandle (ident 0) (ident 0) key₀ ps duplex))))) q13 ≡ nothing
no-raw-handle-allocation = refl
no-raw-captured-mux-monitor : U.step (U.run (B.handler (H.run (M.igStep (IG.monitorCommand (ident 0)))))) q15 ≡ nothing
no-raw-captured-mux-monitor = refl
cmDeliveryTarget : U.State
cmDeliveryTarget = record q15 { base = record (U.base q15) { shutdown = Prior.ownerSending } }
no-cm-delivery-shortcut-after-success : U.step (U.run (B.handler (H.deliverShutdownHandshake (errorId 9)))) cmDeliveryTarget ≡ nothing
no-cm-delivery-shortcut-after-success = refl

-- Conditional current-entry overwrite: outbound uni tracer/key selection still
-- uses the immutable actual birth and original captured handler key.
after : U.Action → U.State → U.State
after action s with U.step action s
... | nothing = s
... | just next = next
uniReturned uniOverwritten uniAllocated : U.State
uniReturned = U.supervised Prior.p12 born ((Fixture.child , U.frame Prior.captured outbound ps unidirectional U.returnedSuccess S.initial) ∷ [])
uniOverwritten = U.setSource (record (U.source uniReturned) { core = M.replaceWorld (O.core (U.source uniReturned))
  (record (M.world (O.core (U.source uniReturned))) { cm = record (Shared.cm (M.world (O.core (U.source uniReturned))))
    { entries = put (ident 0) (Shared.unnegotiated inbound key₁ (ident 99)) (Shared.entries (Shared.cm (M.world (O.core (U.source uniReturned))))) } }) }) uniReturned
uniAllocated = after (U.allocateHandle Fixture.child (ident 0) (ident 0)) uniOverwritten
uni-negotiation-from-real-birth : U.step (U.negotiate Fixture.child ps unidirectional) q12 ≡ just uniReturned
uni-negotiation-from-real-birth = refl
uni-allocation-after-entry-overwrite : U.step (U.allocateHandle Fixture.child (ident 0) (ident 0)) uniOverwritten ≡ just uniAllocated
uni-allocation-after-entry-overwrite = refl
muxAt : MuxId → U.State → Maybe Mux.Mux
muxAt mid s = lookup mid (IG.muxes (IG.execution (M.inboundGovernor (O.core (U.source s)))))
attachmentAt : MuxId → U.State → Maybe Mux.TracerAttachment
attachmentAt mid s with muxAt mid s
... | nothing = nothing
... | just observedMux = just (Mux.tracerAttachment observedMux)
keyAt : MuxId → U.State → Maybe ConnectionKey
keyAt mid s with muxAt mid s
... | nothing = nothing
... | just observedMux = just (Mux.key observedMux)
immutable-outbound-origin-selects-no-tracer : attachmentAt (ident 0) uniAllocated ≡ just Mux.noIGTracer
immutable-outbound-origin-selects-no-tracer = refl
allocation-keeps-original-handler-key : keyAt (ident 0) uniAllocated ≡ just key₀
allocation-keeps-original-handler-key = refl

-- A second actual inbound admission uses the independent accepted socket/key.
-- Both physical children and their immutable origins are created by real forks.
secondCaptured : Shared.HandlerStart
secondCaptured = Shared.handlerStart (ident 1) (ident 1) (ident 1) key₁
secondLease : Shared.Lease
secondLease = Shared.lease w₁ F.binding
sourceWorld : Shared.State
sourceWorld = M.world (O.core (U.source q15))
secondSource : Shared.AdmissionPC → Shared.CMStore → List PromiseId → ℕ →
  Store WorkerId Shared.HandlerStart → Store SocketId Shared.SocketOwner → O.Configuration
secondSource pc cm promises nextPromise handlers socketOwners = record (U.source q15)
  { core = M.replaceWorld (O.core (U.source q15)) (record sourceWorld
    { cm = cm; admissions = put w₁ (Shared.admissionWorker r₁ pc) (Shared.admissions sourceWorld)
    ; promises = promises; nextPromise = nextPromise; handlers = handlers; sockets = socketOwners }) }
firstHeap bothHeap : Shared.EntryHeap
firstHeap = Shared.entries (Shared.cm sourceWorld)
bothHeap = put (ident 1) (Shared.unnegotiated inbound key₁ child₁) firstHeap
bothHandlers : Store WorkerId Shared.HandlerStart
bothHandlers = put child₁ secondCaptured (Shared.handlers sourceWorld)
bothSockets : Store SocketId Shared.SocketOwner
bothSockets = put (ident 1) (Shared.handling child₁) (Shared.sockets sourceWorld)
secondConfig1 secondConfig2 secondConfig3 secondConfig4 secondConfig5 secondConfig6 secondConfig7 : O.Configuration
secondConfig1 = secondSource (Shared.count secondLease)
  (Shared.cmStore (Shared.taken w₁) firstHeap 1) ((ident 0) ∷ []) 1 (Shared.handlers sourceWorld) (Shared.sockets sourceWorld)
secondConfig2 = secondSource (Shared.prepare secondLease)
  (Shared.cmStore (Shared.taken w₁) firstHeap 1) ((ident 0) ∷ []) 1 (Shared.handlers sourceWorld) (Shared.sockets sourceWorld)
secondConfig3 = secondSource (Shared.selectEntry secondLease (ident 1))
  (Shared.cmStore (Shared.taken w₁) firstHeap 1) ((ident 1) ∷ (ident 0) ∷ []) 2 (Shared.handlers sourceWorld) (Shared.sockets sourceWorld)
secondConfig4 = secondSource (Shared.forkHandler secondLease (ident 1) (ident 1))
  (Shared.cmStore (Shared.taken w₁) bothHeap 2) ((ident 1) ∷ (ident 0) ∷ []) 2 (Shared.handlers sourceWorld) (Shared.sockets sourceWorld)
secondConfig5 = secondSource (Shared.publish secondLease (ident 1) (ident 1))
  (Shared.cmStore (Shared.taken w₁) bothHeap 2) ((ident 1) ∷ (ident 0) ∷ []) 2 bothHandlers bothSockets
secondConfig6 = secondSource (Shared.countPublished (ident 1) (ident 1))
  (Shared.cmStore (Shared.full (Shared.insertConnection key₁ (ident 1) F.binding)) bothHeap 2)
  ((ident 1) ∷ (ident 0) ∷ []) 2 bothHandlers bothSockets
secondConfig7 = secondSource (Shared.awaitHandshake (ident 1) (ident 1))
  (Shared.cmStore (Shared.full (Shared.insertConnection key₁ (ident 1) F.binding)) bothHeap 2)
  ((ident 1) ∷ (ident 0) ∷ []) 2 bothHandlers bothSockets
bothOrigins : Store WorkerId Provenance
bothOrigins = born ++ ((child₁ , inbound) ∷ [])
secondBase : O.Configuration → H.Phase → B.State
secondBase c phase = B.supervised c
  (put child₁ (H.handlerThread secondCaptured phase) (B.threads publishedBase)) Close.initialState
d1 : U.State
d1 = U.supervised (record publishedBase { source = secondConfig1 }) born (U.frames q15)
d2 : U.State
d2 = U.supervised (record publishedBase { source = secondConfig2 }) born (U.frames q15)
d3 : U.State
d3 = U.supervised (record publishedBase { source = secondConfig3 }) born (U.frames q15)
d4 : U.State
d4 = U.supervised (record publishedBase { source = secondConfig4 }) born (U.frames q15)
d5 : U.State
d5 = U.supervised (secondBase secondConfig5 H.maskedSetup) bothOrigins (U.frames q15)
d6 : U.State
d6 = U.supervised (secondBase secondConfig6 H.maskedSetup) bothOrigins (U.frames q15)
d7 : U.State
d7 = U.supervised (secondBase secondConfig7 H.maskedSetup) bothOrigins (U.frames q15)
second-birth-step1 : U.step (U.run (B.handler (H.run (M.admissionStep w₁ Server.take)))) q15 ≡ just d1
second-birth-step1 = refl
second-birth-step2 : U.step (U.run (B.handler (H.run (M.admissionStep w₁ Server.countLimit)))) d1 ≡ just d2
second-birth-step2 = refl
second-birth-step3 : U.step (U.run (B.handler (H.run (M.admissionStep w₁ Server.allocatePromise)))) d2 ≡ just d3
second-birth-step3 = refl
second-birth-step4 : U.step (U.run (B.handler (H.run (M.admissionStep w₁ Server.chooseEntry)))) d3 ≡ just d4
second-birth-step4 = refl
second-birth-step5 : U.step (U.run (B.handler (H.run (M.admissionStep w₁ Server.fork)))) d4 ≡ just d5
second-birth-step5 = refl
second-birth-step6 : U.step (U.run (B.handler (H.run (M.admissionStep w₁ Server.putMapBack)))) d5 ≡ just d6
second-birth-step6 = refl
second-birth-step7 : U.step (U.run (B.handler (H.run (M.admissionStep w₁ Server.readCounters)))) d6 ≡ just d7
second-birth-step7 = refl
secondBirthActions : List U.Action
secondBirthActions = (U.run (B.handler (H.run (M.admissionStep w₁ Server.take)))) ∷ (U.run (B.handler (H.run (M.admissionStep w₁ Server.countLimit)))) ∷ (U.run (B.handler (H.run (M.admissionStep w₁ Server.allocatePromise)))) ∷ (U.run (B.handler (H.run (M.admissionStep w₁ Server.chooseEntry)))) ∷ (U.run (B.handler (H.run (M.admissionStep w₁ Server.fork)))) ∷ (U.run (B.handler (H.run (M.admissionStep w₁ Server.putMapBack)))) ∷ (U.run (B.handler (H.run (M.admissionStep w₁ Server.readCounters)))) ∷ []
second-birth-path : U.Executes q15 secondBirthActions d7
second-birth-path = U.next second-birth-step1 (U.next second-birth-step2 (U.next second-birth-step3 (U.next second-birth-step4 (U.next second-birth-step5 (U.next second-birth-step6 (U.next second-birth-step7 (U.done)))))))
publicationActions : List U.Action
publicationActions = U.negotiate Fixture.child ps duplex ∷ U.allocateHandle Fixture.child (ident 0) (ident 0) ∷ U.publishSuccess Fixture.child ∷ []
publication-path : U.Executes q12 publicationActions q15
publication-path = U.next actual-negotiate (U.next actual-handle-allocation (U.next actual-coupled-publication U.done))
abstract
  initialized-two-physical-handlers : U.Executes q₀ ((birthActions ++ publicationActions) ++ secondBirthActions) d7
  initialized-two-physical-handlers = append (append initialized-birth publication-path) second-birth-path
secondHandshake secondReturned secondAllocated secondPublished : U.State
secondHandshake = record d7 { base = secondBase secondConfig7 H.handshaking }
secondReturned = after (U.negotiate child₁ ps unidirectional) secondHandshake
secondAllocated = after (U.allocateHandle child₁ (ident 1) (ident 1)) secondReturned
secondPublished = after (U.publishSuccess child₁) secondAllocated
second-enters-handshake : U.step (U.run (B.handler (H.enterHandshake child₁))) d7 ≡ just secondHandshake
second-enters-handshake = refl
second-handshake-returns : U.step (U.negotiate child₁ ps unidirectional) secondHandshake ≡ just secondReturned
second-handshake-returns = refl
second-actual-handle-allocation : U.step (U.allocateHandle child₁ (ident 1) (ident 1)) secondReturned ≡ just secondAllocated
second-actual-handle-allocation = refl
second-actual-coupled-publication : U.step (U.publishSuccess child₁) secondAllocated ≡ just secondPublished
second-actual-coupled-publication = refl
inbound-uni-birth-keeps-ig-tracer : attachmentAt (ident 1) secondAllocated ≡ just Mux.igTracer
inbound-uni-birth-keeps-ig-tracer = refl
second-success-visible-before-buffer : lookup (ident 1) (Shared.handshakeResults (M.world (O.core (U.source secondPublished)))) ≡ just (Shared.negotiated (ident 1) unidirectional)
second-success-visible-before-buffer = refl
second-published-frame : S.State → U.Frame
second-published-frame stage = U.frame secondCaptured inbound ps unidirectional (U.promisePublished (ident 1) (ident 1)) stage
twoAt : S.State → S.State → U.State
twoAt firstStage secondStage = U.supervised (U.base secondPublished) bothOrigins
  ((Fixture.child , publishedFrame firstStage) ∷ (child₁ , second-published-frame secondStage) ∷ [])
t1 : U.State
t1 = twoAt Stages.s₂ Stages.s₁
independent-step1 : U.step (U.startupStep Fixture.child S.allocateBuffer) secondPublished ≡ just t1
independent-step1 = refl
t2 : U.State
t2 = twoAt Stages.s₂ Stages.s₂
independent-step2 : U.step (U.startupStep child₁ S.allocateBuffer) t1 ≡ just t2
independent-step2 = refl
t3 : U.State
t3 = twoAt Stages.s₃ Stages.s₂
independent-step3 : U.step (U.startupStep Fixture.child S.createBearer) t2 ≡ just t3
independent-step3 = refl
t4 : U.State
t4 = twoAt Stages.s₃ Stages.s₃
independent-step4 : U.step (U.startupStep child₁ S.createBearer) t3 ≡ just t4
independent-step4 = refl
t5 : U.State
t5 = twoAt Stages.s₄ Stages.s₃
independent-step5 : U.step (U.startupStep Fixture.child S.enterRun) t4 ≡ just t5
independent-step5 = refl
t6 : U.State
t6 = twoAt Stages.s₄ Stages.s₄
independent-step6 : U.step (U.startupStep child₁ S.enterRun) t5 ≡ just t6
independent-step6 = refl
t7 : U.State
t7 = twoAt Stages.s₅ Stages.s₄
independent-step7 : U.step (U.startupStep Fixture.child S.traceStarting) t6 ≡ just t7
independent-step7 = refl
t8 : U.State
t8 = twoAt Stages.s₅ Stages.s₅
independent-step8 : U.step (U.startupStep child₁ S.traceStarting) t7 ≡ just t8
independent-step8 = refl
t9 : U.State
t9 = twoAt Stages.s₆ Stages.s₅
independent-step9 : U.step (U.startupStep Fixture.child S.allocateEgress) t8 ≡ just t9
independent-step9 = refl
t10 : U.State
t10 = twoAt Stages.s₆ Stages.s₆
independent-step10 : U.step (U.startupStep child₁ S.allocateEgress) t9 ≡ just t10
independent-step10 = refl
t11 : U.State
t11 = twoAt Stages.s₇ Stages.s₆
independent-step11 : U.step (U.startupStep Fixture.child S.openPool) t10 ≡ just t11
independent-step11 = refl
t12 : U.State
t12 = twoAt Stages.s₇ Stages.s₇
independent-step12 : U.step (U.startupStep child₁ S.openPool) t11 ≡ just t12
independent-step12 = refl
other-handler-does-not-advance : S.phase (U.startupAt child₁ t1) ≡ S.published
other-handler-does-not-advance = refl
first-global-fork historicalReturn historicalQueued historicalRegistered historicalRemoved historicalResult : U.State
first-global-fork = twoAt Stages.s₈ Stages.s₇
historicalReturn = twoAt Stages.fast₁ Stages.s₇
historicalQueued = twoAt Stages.fast₂ Stages.s₇
historicalRegistered = twoAt Stages.fast₃ Stages.s₇
historicalRemoved = twoAt Stages.fast₄ Stages.s₇
historicalResult = twoAt Stages.fast₅ Stages.s₇
first-global-fork-step : U.step (U.startupStep Fixture.child (S.forkMuxer (ident 0))) t12 ≡ just first-global-fork
first-global-fork-step = refl
cross-pool-active-id-reuse-refused : U.step (U.startupStep child₁ (S.forkMuxer (ident 0))) first-global-fork ≡ nothing
cross-pool-active-id-reuse-refused = refl
fast-engine-return : U.step (U.startupStep Fixture.child (S.child (S.bodyReturned (ident 0) tt))) first-global-fork ≡ just historicalReturn
fast-engine-return = refl
fast-engine-publication : U.step (U.startupStep Fixture.child (S.child (S.publishCompletion (ident 0)))) historicalReturn ≡ just historicalQueued
fast-engine-publication = refl
fast-engine-parent-registers : U.step (U.startupStep Fixture.child S.registerMuxer) historicalQueued ≡ just historicalRegistered
fast-engine-parent-registers = refl
fast-engine-deregisters : U.step (U.startupStep Fixture.child (S.child (S.deregister (ident 0)))) historicalRegistered ≡ just historicalRemoved
fast-engine-deregisters = refl
fast-engine-async-result : U.step (U.startupStep Fixture.child (S.child (S.publishAsyncResult (ident 0)))) historicalRemoved ≡ just historicalResult
fast-engine-async-result = refl
removed-history-is-not-fresh : U.step (U.startupStep child₁ (S.forkMuxer (ident 0))) historicalResult ≡ nothing
removed-history-is-not-fresh = refl
fresh-second-pool-fork : U.step (U.startupStep child₁ (S.forkMuxer (ident 2))) historicalResult ≡ just
  (twoAt Stages.fast₅ (S.startupState (S.muxerForked (ident 2))
    (record Pool.initial { handles = ((ident 2) , Pool.bodyRunning) ∷ []; parentFork = just (ident 2) })))
fresh-second-pool-fork = refl
secondSuccessActions : List U.Action
secondSuccessActions = U.run (B.handler (H.enterHandshake child₁)) ∷ U.negotiate child₁ ps unidirectional ∷ U.allocateHandle child₁ (ident 1) (ident 1) ∷ U.publishSuccess child₁ ∷ []
second-success-path : U.Executes d7 secondSuccessActions secondPublished
second-success-path = U.next second-enters-handshake (U.next second-handshake-returns (U.next second-actual-handle-allocation (U.next second-actual-coupled-publication U.done)))
independentActions : List U.Action
independentActions = (U.startupStep Fixture.child S.allocateBuffer) ∷ (U.startupStep child₁ S.allocateBuffer) ∷ (U.startupStep Fixture.child S.createBearer) ∷ (U.startupStep child₁ S.createBearer) ∷ (U.startupStep Fixture.child S.enterRun) ∷ (U.startupStep child₁ S.enterRun) ∷ (U.startupStep Fixture.child S.traceStarting) ∷ (U.startupStep child₁ S.traceStarting) ∷ (U.startupStep Fixture.child S.allocateEgress) ∷ (U.startupStep child₁ S.allocateEgress) ∷ (U.startupStep Fixture.child S.openPool) ∷ (U.startupStep child₁ S.openPool) ∷ []
independent-startup-path : U.Executes secondPublished independentActions t12
independent-startup-path = U.next independent-step1 (U.next independent-step2 (U.next independent-step3 (U.next independent-step4 (U.next independent-step5 (U.next independent-step6 (U.next independent-step7 (U.next independent-step8 (U.next independent-step9 (U.next independent-step10 (U.next independent-step11 (U.next independent-step12 (U.done))))))))))))
historyActions : List U.Action
historyActions = U.startupStep Fixture.child (S.forkMuxer (ident 0)) ∷
  U.startupStep Fixture.child (S.child (S.bodyReturned (ident 0) tt)) ∷
  U.startupStep Fixture.child (S.child (S.publishCompletion (ident 0))) ∷
  U.startupStep Fixture.child S.registerMuxer ∷
  U.startupStep Fixture.child (S.child (S.deregister (ident 0))) ∷
  U.startupStep Fixture.child (S.child (S.publishAsyncResult (ident 0))) ∷ []
history-path : U.Executes t12 historyActions historicalResult
history-path = U.next first-global-fork-step (U.next fast-engine-return (U.next fast-engine-publication
  (U.next fast-engine-parent-registers (U.next fast-engine-deregisters (U.next fast-engine-async-result U.done)))))
abstract
  initialized-independent-startups-with-history : U.Executes q₀
    ((((birthActions ++ publicationActions) ++ secondBirthActions) ++ secondSuccessActions) ++ (independentActions ++ historyActions)) historicalResult
  initialized-independent-startups-with-history = append (append initialized-two-physical-handlers second-success-path)
    (append independent-startup-path history-path)

-- Per-handler masking is independent: a fresh engine in the second pool can
-- fork while the first parent's insertion is still pending.
second-forks-during-first-parent-gap : U.step (U.startupStep child₁ (S.forkMuxer (ident 2))) first-global-fork ≡ just
  (twoAt Stages.s₈ (S.startupState (S.muxerForked (ident 2))
    (record Pool.initial { handles = ((ident 2) , Pool.bodyRunning) ∷ []; parentFork = just (ident 2) })))
second-forks-during-first-parent-gap = refl

-- The source CM caller and IG can consume success and enqueue responder starts
-- before buffer allocation or physical muxer/demuxer startup.
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.CSP.GovernorLifecycle as Lifecycle
c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : U.State
c1 = U.setSource (Fixture.withHandle (Fixture.at Fixture.wait Fixture.published)) q15
c2 = U.setSource (Fixture.withHandle (Fixture.at (A.commitResult (ident 0) key₀ (Shared.negotiated (ident 0) duplex)) Fixture.published)) q15
c3 = U.setSource (Fixture.withHandle (Fixture.at (A.count (A.complete (Cases.connected key₀ duplex (ident 0)))) Fixture.negotiated)) q15
c4 = U.setSource (Fixture.withHandle (Fixture.at (A.complete (Cases.connected key₀ duplex (ident 0))) Fixture.negotiated)) q15
c5 = U.setSource Fixture.returned q15
c6 = U.setSource Lifecycle.ig2 q15
c7 = U.setSource Lifecycle.ig3 q15
c8 = U.setSource Lifecycle.ig4 q15
c9 = U.setSource Lifecycle.ig5 q15
c10 = U.setSource Lifecycle.ig6 q15
c11 = U.setSource Lifecycle.ig7 q15
caller-queue-step1 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.readCounters))) q15 ≡ just c1
caller-queue-step1 = refl
caller-queue-step2 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.readResult))) c1 ≡ just c2
caller-queue-step2 = refl
caller-queue-step3 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.commitHandshake))) c2 ≡ just c3
caller-queue-step3 = refl
caller-queue-step4 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.readCounters))) c3 ≡ just c4
caller-queue-step4 = refl
caller-queue-step5 : U.step (U.run (B.outbound (O.acquire Fixture.caller A.returnResult))) c4 ≡ just c5
caller-queue-step5 = refl
caller-queue-step6 : U.step (U.run (B.handler (H.run (M.igStep (IG.captureTime 0))))) c5 ≡ just c6
caller-queue-step6 = refl
caller-queue-step7 : U.step (U.run (B.handler (H.run (M.igStep IG.registerInactivity)))) c6 ≡ just c7
caller-queue-step7 = refl
caller-queue-step8 : U.step (U.run (B.handler (H.run (M.igStep IG.selectBatch)))) c7 ≡ just c8
caller-queue-step8 = refl
caller-queue-step9 : U.step (U.run (B.handler (H.run (M.igStep IG.readEvent)))) c8 ≡ just c9
caller-queue-step9 = refl
caller-queue-step10 : U.step (U.run (B.handler (H.run (M.igStep IG.registerIdleTimer)))) c9 ≡ just c10
caller-queue-step10 = refl
caller-queue-step11 : U.step (U.run (B.handler (H.run (M.igStep IG.runResponders)))) c10 ≡ just c11
caller-queue-step11 = refl
callerQueueActions : List U.Action
callerQueueActions = (U.run (B.outbound (O.acquire Fixture.caller A.readCounters))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.readResult))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.commitHandshake))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.readCounters))) ∷ (U.run (B.outbound (O.acquire Fixture.caller A.returnResult))) ∷ (U.run (B.handler (H.run (M.igStep (IG.captureTime 0))))) ∷ (U.run (B.handler (H.run (M.igStep IG.registerInactivity)))) ∷ (U.run (B.handler (H.run (M.igStep IG.selectBatch)))) ∷ (U.run (B.handler (H.run (M.igStep IG.readEvent)))) ∷ (U.run (B.handler (H.run (M.igStep IG.registerIdleTimer)))) ∷ (U.run (B.handler (H.run (M.igStep IG.runResponders)))) ∷ []
caller-queue-path : U.Executes q15 callerQueueActions c11
caller-queue-path = U.next caller-queue-step1 (U.next caller-queue-step2 (U.next caller-queue-step3 (U.next caller-queue-step4 (U.next caller-queue-step5 (U.next caller-queue-step6 (U.next caller-queue-step7 (U.next caller-queue-step8 (U.next caller-queue-step9 (U.next caller-queue-step10 (U.next caller-queue-step11 (U.done)))))))))))
abstract
  initialized-requests-before-startup : U.Executes q₀
    ((birthActions ++ publicationActions) ++ callerQueueActions) c11
  initialized-requests-before-startup = append (append initialized-birth publication-path) caller-queue-path
queued-before-buffer-startup-phase : S.phase (U.startupAt Fixture.child c11) ≡ S.published
queued-before-buffer-startup-phase = refl
queued-before-buffer-no-physical-jobs : Pool.handles (S.pool (U.startupAt Fixture.child c11)) ≡ []
queued-before-buffer-no-physical-jobs = refl
commandsAt : MuxId → U.State → Maybe (List Mux.Command)
commandsAt mid s with muxAt mid s
... | nothing = nothing
... | just observedMux = just (Mux.commands observedMux)
actual-start-request-queued-before-startup : commandsAt (ident 0) c11 ≡ just (Mux.startCommand G.proto ∷ [])
actual-start-request-queued-before-startup = refl

foreign-pool-body-result-refused : U.step (U.startupStep child₁ (S.child (S.bodyReturned (ident 0) tt))) first-global-fork ≡ nothing
foreign-pool-body-result-refused = refl
unknown-handler-startup-refused : U.step (U.startupStep (ident 99) S.allocateBuffer) q15 ≡ nothing
unknown-handler-startup-refused = refl

-- Generic evidence is applied to the actual initialized 27-action prefix.
import ConnectionManagement.Properties.MuxHandlerSupervision as Properties
module Facts = Properties ⊤
import ConnectionManagement.Properties.MuxStartup as StartupProperties
module StartupFacts = StartupProperties ⊤
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import Data.List.Relation.Unary.All as All
open import Data.Product using (Σ; _×_)
initial-bounds : SupplyBounds (M.world F.start)
initial-bounds = All.[] , All.[]
abstract
  actual-projections : Facts.Paths q₀ q27
  actual-projections = Facts.exec-projects initialized-monitor-entry
actual-source-trace : Σ (List O.Action) (λ actions → O.Executes (U.source q₀) actions (U.source q27))
actual-source-trace = Facts.machine actual-projections
actual-coordinator-trace : Σ (List Close.Action) (λ actions → Close.Executes
  (B.shutdown (U.base q₀)) actions (B.shutdown (U.base q27)))
actual-coordinator-trace = Facts.coordinator actual-projections
actual-selected-worker-startup : Facts.STrace S.initial (U.startupAt Fixture.child q27)
actual-selected-worker-startup = Facts.startup-from-initial actual-initializer initialized-monitor-entry Fixture.child
abstract
  actual-monitoring-pair-and-pool-trace : StartupFacts.Pair (ident 0) (ident 1) (S.pool (U.startupAt Fixture.child q27)) ×
    StartupFacts.PoolTrace Pool.initial (S.pool (U.startupAt Fixture.child q27))
  actual-monitoring-pair-and-pool-trace = Facts.monitoring-from-initial actual-initializer initialized-monitor-entry Fixture.child (ident 0) (ident 1) refl
actual-publication-coupling : Facts.Publication Fixture.child q14 q15
actual-publication-coupling = Facts.publication-observation Fixture.child q14 actual-coupled-publication
initialized-captures-valid : Capture.Captures (U.source q27)
initialized-captures-valid = Facts.from-initial-captures actual-initializer initialized-monitor-entry
initialized-supply-valid : Supply.Valid (U.source q27)
initialized-supply-valid = Facts.from-initial-supply actual-initializer initial-bounds initialized-monitor-entry
second-worker-startup-history : Facts.STrace S.initial (U.startupAt child₁ historicalResult)
second-worker-startup-history = Facts.startup-from-initial actual-initializer initialized-independent-startups-with-history child₁
two-handler-runtime-supply-valid : Supply.Valid (U.source historicalResult)
two-handler-runtime-supply-valid = Facts.from-initial-supply actual-initializer initial-bounds initialized-independent-startups-with-history
engine-result-keeps-parent-registry : B.threads (U.base historicalResult) ≡ B.threads (U.base historicalRemoved)
engine-result-keeps-parent-registry = Facts.startup-parent-registry Fixture.child (S.child (S.publishAsyncResult (ident 0))) historicalRemoved fast-engine-async-result
engine-result-is-not-parent-result : H.resultReady Fixture.child (B.view (U.base historicalResult)) ≡ false
engine-result-is-not-parent-result = refl


-- The inherited empty CM snapshot still closes through the new wrapper; its
-- certificate concerns that snapshot and does not assert future quiescence.
import ConnectionManagement.Properties.HandlerSupervision as HandlerFacts
emptySnapshot emptyWaiting emptyFinished : U.State
emptySnapshot = record q₀ { base = record (U.base q₀)
  { shutdown = Close.shutdownState Close.reading [] [] [] } }
emptyWaiting = record q₀ { base = record (U.base q₀)
  { shutdown = Close.shutdownState Close.awaitResults [] [] [] } }
emptyFinished = record q₀ { base = record (U.base q₀)
  { shutdown = Close.shutdownState Close.closed [] [] [] } }
empty-capture-step : U.step (U.run (B.handler (H.shutdownStep Close.captureSnapshot))) q₀ ≡ just emptySnapshot
empty-capture-step = refl
empty-traversal-step : U.step (U.run (B.handler (H.shutdownStep Close.finishTraversal))) emptySnapshot ≡ just emptyWaiting
empty-traversal-step = refl
empty-close-step : U.step (U.run (B.handler (H.shutdownStep Close.finishClose))) emptyWaiting ≡ just emptyFinished
empty-close-step = refl
emptyCloseActions : List U.Action
emptyCloseActions = U.run (B.handler (H.shutdownStep Close.captureSnapshot)) ∷
  U.run (B.handler (H.shutdownStep Close.finishTraversal)) ∷
  U.run (B.handler (H.shutdownStep Close.finishClose)) ∷ []
empty-close-path : U.Executes q₀ emptyCloseActions emptyFinished
empty-close-path = U.next empty-capture-step (U.next empty-traversal-step (U.next empty-close-step U.done))
empty-close-certificate : Close.remaining (B.shutdown (U.base emptyFinished)) ≡ [] ×
  HandlerFacts.PhysicalWait (B.shutdown (U.base emptyFinished))
empty-close-certificate = Facts.closed-from-initial actual-initializer empty-close-path refl
