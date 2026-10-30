{-# OPTIONS --guardedness #-}

-- Finite counterexample: closing owned Server/IG/CM scopes does not finish a
-- raw admission Async. Two explicit handoffs reconstruct the existing fixture;
-- worker zero is certified at its actual empty-promise wait, not merely stored.
module ConnectionManagement.Negative.ServerAdmission where

open import Data.Bool using (Bool; true; false)
import Data.Empty
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.Properties.ServerAdmission as Proof
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Negative.MuxPublicationInbound as B
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.MuxStartupUnwindFixtures as Fixture
import ConnectionManagement.Scenarios.Admission as Admission
import ConnectionManagement.CSP.Fixtures as Source
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.Properties.PromiseWait as PromiseWait
private
  module S = Server I.bearerClosed
  module Facts = Proof I.bearerClosed
  module N = Publication I.bearerClosed
  module C = N.C
  module D = N.D
  module R = N.R
  module X = D.X
  module W = N.W
  module G = N.G
  module M = N.M
  module P = N.P
  module F = Fixture I.bearerClosed I.owner I.captured (ident 0)
  module Selected = B.NewMuxSync

wrap : P.State → N.State
wrap p = N.publicationState (C.catchState (D.deltaQState (R.unwinding
  (W.handlerExitState (G.shutdownState (M.monitorState p []) []) []) []) []) []) []
bareWorld : Shared.State
bareWorld = Shared.state Admission.emptyCM [] [] [] [] 0 [] [] []
oneWorld : Shared.State
oneWorld = Shared.state Admission.emptyCM
  ((Admission.w₀ , Shared.admissionWorker Admission.r₀ Shared.acquireMap) ∷ []) []
  ((ident 0 , Shared.admitting Admission.w₀) ∷ []) [] 0 [] [] []
baseAt : Shared.State → N.State
baseAt world = wrap (I.pre (Machine.initial Shared.responderMode world))
workersOne workersTwo : Store WorkerId S.Worker
workersOne = (Admission.w₀ , S.rawWorker Admission.r₀ S.calling 0) ∷ []
workersTwo = workersOne ++ ((Admission.w₁ , S.rawWorker Admission.r₁ S.calling 0) ∷ [])
start one born : S.State
start = S.serverState (baseAt bareWorld) [] S.serving true
one = S.serverState (baseAt oneWorld) workersOne S.serving true
born = S.serverState B.initial workersTwo S.serving true
actual-initializer : S.initial (O.initial (Machine.initial Shared.responderMode bareWorld)) ≡ just start
actual-initializer = refl
no-adoption : S.initial (O.initial Source.start) ≡ nothing
no-adoption = refl
fork-one : S.step (S.acceptedFork Admission.w₀ Admission.r₀) start ≡ just one
fork-one = refl
fork-two : S.step (S.acceptedFork Admission.w₁ Admission.r₁) one ≡ just born
fork-two = refl

permissions : All.All
  (λ a → ∀ current → S.allowed a (S.serverState current workersTwo S.serving true) ≡ true)
  Selected.actions
permissions = (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ (λ _ → refl) All.∷ All.[]
faultEnded : S.State
faultEnded = S.serverState Selected.s10 workersTwo S.serving true
physical-prefix : S.Executes born (map S.run Selected.actions) faultEnded
physical-prefix = Facts.lift-run workersTwo S.serving true permissions Selected.initialized

-- Concrete shared IG cleanup is retained; no success oracle closes its scope.
inactiveGovernor flushedGovernor : IG.Runtime
inactiveGovernor = IG.runtimeState IG.emptyPublished 0 IG.exitFlush (IG.engine [] [] [] false 0)
flushedGovernor = record inactiveGovernor { continuation = IG.exited }
withGovernor : IG.Runtime → S.State → S.State
withGovernor r s = S.setSource (record (S.source s)
  { core = record (O.core (S.source s)) { inboundGovernor = r } }) s
atBeforeIG : S.Stage → S.State
atBeforeIG pc = record faultEnded { stage = pc; listenerOpen = listener pc }
  where
  listener : S.Stage → Bool
  listener S.acceptBodyExited = false
  listener S.acceptResultAvailable = false
  listener S.acceptJoined = false
  listener S.serverStopped = false
  listener S.actionJoined = false
  listener S.igCancelRequested = false
  listener S.igCancelDelivered = false
  listener _ = true
inactive flushed : S.State
inactive = withGovernor inactiveGovernor (record faultEnded { stage = S.igInactive; listenerOpen = false })
flushed = withGovernor flushedGovernor (record inactive { stage = S.igFlushed })
atAfterIG : S.Stage → S.State
atAfterIG pc = record flushed { stage = pc }
scope1 : S.step (S.scope S.returnAction) faultEnded ≡ just (atBeforeIG S.actionBodyExited)
scope1 = refl
scope2 : S.step (S.scope S.publishActionResult) (atBeforeIG S.actionBodyExited) ≡ just (atBeforeIG S.actionResultAvailable)
scope2 = refl
scope3 : S.step (S.scope S.selectActionWinner) (atBeforeIG S.actionResultAvailable) ≡ just (atBeforeIG S.closingAccept)
scope3 = refl
scope4 : S.step (S.scope S.requestAcceptCancel) (atBeforeIG S.closingAccept) ≡ just (atBeforeIG S.acceptCancelRequested)
scope4 = refl
scope5 : S.step (S.scope S.deliverAcceptAtWait) (atBeforeIG S.acceptCancelRequested) ≡ just (atBeforeIG S.acceptCancelDelivered)
scope5 = refl
scope6 : S.step (S.scope S.closeListener) (atBeforeIG S.acceptCancelDelivered) ≡ just (atBeforeIG S.acceptBodyExited)
scope6 = refl
scope7 : S.step (S.scope S.publishAcceptResult) (atBeforeIG S.acceptBodyExited) ≡ just (atBeforeIG S.acceptResultAvailable)
scope7 = refl
scope8 : S.step (S.scope S.joinAccept) (atBeforeIG S.acceptResultAvailable) ≡ just (atBeforeIG S.acceptJoined)
scope8 = refl
scope9 : S.step (S.scope S.traceStopped) (atBeforeIG S.acceptJoined) ≡ just (atBeforeIG S.serverStopped)
scope9 = refl
scope10 : S.step (S.scope S.cancelJoinReturnedAction) (atBeforeIG S.serverStopped) ≡ just (atBeforeIG S.actionJoined)
scope10 = refl
scope11 : S.step (S.scope S.requestIGCancel) (atBeforeIG S.actionJoined) ≡ just (atBeforeIG S.igCancelRequested)
scope11 = refl
scope12 : S.step (S.scope S.deliverIGBody) (atBeforeIG S.igCancelRequested) ≡ just (atBeforeIG S.igCancelDelivered)
scope12 = refl
scope13 : S.step (S.scope S.deactivateIG) (atBeforeIG S.igCancelDelivered) ≡ just inactive
scope13 = refl
scope14 : S.step (S.scope S.flushIG) inactive ≡ just flushed
scope14 = refl
scope15 : S.step (S.scope S.finishIGBody) flushed ≡ just (atAfterIG S.igBodyExited)
scope15 = refl
scope16 : S.step (S.scope S.publishIGResult) (atAfterIG S.igBodyExited) ≡ just (atAfterIG S.igResultAvailable)
scope16 = refl
scope17 : S.step (S.scope S.joinIG) (atAfterIG S.igResultAvailable) ≡ just (atAfterIG S.igJoined)
scope17 = refl
scope18 : S.step (S.scope S.beginCM) (atAfterIG S.igJoined) ≡ just (atAfterIG S.closingCM)
scope18 = refl
scopeActions : List S.Action
scopeActions = S.scope S.returnAction ∷ S.scope S.publishActionResult ∷ S.scope S.selectActionWinner ∷ S.scope S.requestAcceptCancel ∷ S.scope S.deliverAcceptAtWait ∷ S.scope S.closeListener ∷ S.scope S.publishAcceptResult ∷ S.scope S.joinAccept ∷ S.scope S.traceStopped ∷ S.scope S.cancelJoinReturnedAction ∷ S.scope S.requestIGCancel ∷ S.scope S.deliverIGBody ∷ S.scope S.deactivateIG ∷ S.scope S.flushIG ∷ S.scope S.finishIGBody ∷ S.scope S.publishIGResult ∷ S.scope S.joinIG ∷ S.scope S.beginCM ∷ []
scopePath : S.Executes faultEnded scopeActions (atAfterIG S.closingCM)
scopePath = S.next scope1 (S.next scope2 (S.next scope3 (S.next scope4 (S.next scope5 (S.next scope6 (S.next scope7 (S.next scope8 (S.next scope9 (S.next scope10 (S.next scope11 (S.next scope12 (S.next scope13 (S.next scope14 (S.next scope15 (S.next scope16 (S.next scope17 (S.next scope18 (S.done))))))))))))))))))

withCM : Close.State → S.State → S.State
withCM pc s = record s { base = record (S.base s) { base = record (N.base (S.base s))
  { base = record (C.base (N.base (S.base s))) { base = F.withShutdown pc (N.raw (S.base s)) } } } }
cmReading cmWaiting cmClosed returnedServer : S.State
cmReading = withCM (Close.shutdownState Close.reading [] [] []) (atAfterIG S.closingCM)
cmWaiting = withCM (Close.shutdownState Close.awaitResults [] [] []) (atAfterIG S.closingCM)
cmClosed = withCM (Close.shutdownState Close.closed [] [] []) (atAfterIG S.closingCM)
returnedServer = record cmClosed { stage = S.serverReturned }
cmAction : Close.Action → S.Action
cmAction a = S.run (B.runR (R.run (X.run (W.shutdownStep a))))
cm1 : S.step (cmAction Close.captureSnapshot) (atAfterIG S.closingCM) ≡ just cmReading
cm1 = refl
cm2 : S.step (cmAction Close.finishTraversal) cmReading ≡ just cmWaiting
cm2 = refl
cm3 : S.step (cmAction Close.finishClose) cmWaiting ≡ just cmClosed
cm3 = refl
final : S.step (S.scope S.finishServer) cmClosed ≡ just returnedServer
final = refl
append : ∀ {a as b bs c} → S.Executes a as b → S.Executes b bs c → S.Executes a (as ++ bs) c
append S.done tail = tail
append (S.next eq rest) tail = S.next eq (append rest tail)
allActions : List S.Action
allActions = S.acceptedFork Admission.w₀ Admission.r₀ ∷ S.acceptedFork Admission.w₁ Admission.r₁ ∷
  (map S.run Selected.actions ++ (scopeActions ++
    (cmAction Close.captureSnapshot ∷ cmAction Close.finishTraversal ∷ cmAction Close.finishClose ∷ S.scope S.finishServer ∷ [])))
abstract
  initialized : S.Executes start allActions returnedServer
  initialized = S.next fork-one (S.next fork-two (append physical-prefix
    (append scopePath (S.next cm1 (S.next cm2 (S.next cm3 (S.next final S.done)))))))
server-has-returned : S.stage returnedServer ≡ S.serverReturned
server-has-returned = refl
listener-closed : S.listenerOpen returnedServer ≡ false
listener-closed = refl
handler-result : W.resultReady I.owner (R.base (N.raw (S.base returnedServer))) ≡ true
handler-result = refl
admission-not-finished : S.resultOf Admission.w₀ returnedServer ≡ nothing
admission-not-finished = refl
actual-raw-worker : lookup Admission.w₀ (S.workers returnedServer) ≡ just (S.rawWorker Admission.r₀ S.calling 0)
actual-raw-worker = refl
not-all-workers-finished : S.allResults (S.workers returnedServer) ≡ false
not-all-workers-finished = refl
caller-at-promise-wait : lookup Admission.w₀ (Shared.admissions (S.shared returnedServer)) ≡
  just (Shared.admissionWorker Admission.r₀ (Shared.awaitHandshake (ident 0) (ident 0)))
caller-at-promise-wait = refl
promise-empty : lookup (ident 0) (Shared.handshakeResults (S.shared returnedServer)) ≡ nothing
promise-empty = refl
raw-read-retries : Machine.advance (Machine.handshakeStep Admission.w₀ Handshake.readResult)
  (O.core (S.source returnedServer)) ≡ nothing
raw-read-retries = PromiseWait.inbound-read-retries (O.core (S.source returnedServer))
  Admission.w₀ Admission.r₀ (ident 0) (ident 0) caller-at-promise-wait promise-empty
map-purged : Shared.mapCell (Shared.cm (S.shared returnedServer)) ≡ Shared.full []
map-purged = refl
no-fake-worker-result : S.step (S.workerResult Admission.w₀) returnedServer ≡ nothing
no-fake-worker-result = refl
no-unread-return : S.step (S.workerReturned Admission.w₀) returnedServer ≡ nothing
no-unread-return = refl
no-new-handoff-after-close : S.step (S.acceptedFork (ident 20) Admission.r₀) returnedServer ≡ nothing
no-new-handoff-after-close = refl
no-shortcut-close : S.step (S.scope S.finishServer) faultEnded ≡ nothing
no-shortcut-close = refl

-- The claimed implication is refuted by an actual finite run, rather than by
-- an arbitrary forged logical admission or physical-worker table.
false-implies-true : false ≡ true → Data.Empty.⊥
false-implies-true ()
no-universal-all-worker-completion :
  (∀ {t} (as : List S.Action) → S.Executes start as t → S.stage t ≡ S.serverReturned →
    S.allResults (S.workers t) ≡ true) → Data.Empty.⊥
no-universal-all-worker-completion claim = false-implies-true (claim allActions initialized refl)

-- A later observed exception can still finish the worker. This models the
-- replay harness's explicit cancellation, not automatic Server cleanup or an
-- assumption of permanent blocking; its socket close is outside the CM API.
recoveryError : S.Fault
recoveryError = S.async (errorId 123)
recovering recoveryBody recovered : S.State
recovering = S.setPC Admission.w₀ (S.rawWorker Admission.r₀ S.calling 0) (S.closeException recoveryError) returnedServer
recoveryBody = record returnedServer { workers = put Admission.w₀
  (S.rawWorker Admission.r₀ (S.bodyExited (S.raised recoveryError)) 1) (S.workers returnedServer) }
recovered = S.setPC Admission.w₀ (S.rawWorker Admission.r₀ (S.bodyExited (S.raised recoveryError)) 1)
  (S.resultAvailable (S.raised recoveryError)) recoveryBody
recovery1 : S.step (S.workerException Admission.w₀ recoveryError) returnedServer ≡ just recovering
recovery1 = refl
no-result-before-worker-close : S.step (S.workerResult Admission.w₀) recovering ≡ nothing
no-result-before-worker-close = refl
recovery2 : S.step (S.workerClose Admission.w₀ nothing) recovering ≡ just recoveryBody
recovery2 = refl
recovery3 : S.step (S.workerResult Admission.w₀) recoveryBody ≡ just recovered
recovery3 = refl
recovery-result : S.resultOf Admission.w₀ recovered ≡ just (S.raised recoveryError)
recovery-result = refl
no-dead-worker-reuse : S.step (S.run (S.runMachine (Machine.handshakeStep Admission.w₀ Handshake.readResult))) recovered ≡ nothing
no-dead-worker-reuse = refl

no-historical-worker-outbound-reuse : S.step (S.run (S.runOutbound
  (O.beginAcquire Admission.w₀ (Acquire.acquireRequest (remote Admission.key₀)
    (ident 20) (ident 20) outbound nothing)))) recovered ≡ nothing
no-historical-worker-outbound-reuse = refl
