{-# OPTIONS --guardedness #-}

-- Prehandshake physical handlers: actual admission/fork, the unmasked handshake
-- catch's promise write, finally cleanup, Async result and CM snapshot wait.
-- This does not fabricate successful handshakes or post-handshake mux closure.
module ConnectionManagement.Negative.HandlerSupervision where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.HandlerSupervision as HS
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as S
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.HandlerEstablishment as E
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀; key₀)

err closeErr : ErrorId
err = errorId 9
closeErr = errorId 91
captured : S.HandlerStart
captured = S.handlerStart (ident 0) (ident 0) (ident 0) key₀
at : Machine.Configuration → Maybe HS.Phase → Close.State → HS.State
at c nothing owner = HS.supervised c [] owner
at c (just phase) owner = HS.supervised c ((child₀ , HS.handlerThread captured phase) ∷ []) owner
h₀ : HS.State
h₀ = at F.start nothing Close.initialState
actual-empty-initializer : HS.initial F.start ≡ just h₀
actual-empty-initializer = refl
pre1 pre2 pre6 : Machine.Configuration
pre1 = F.pre (S.cmStore (S.taken w₀) [] 0) (S.count F.parentLease) [] 0
pre2 = F.pre (S.cmStore (S.taken w₀) [] 0) (S.prepare F.parentLease) [] 0
pre6 = F.snapshot F.unneg (S.full F.binding) (S.countPublished (ident 0) (ident 0)) (S.handling child₀) [] [] []
p1 p2 p3 p4 p5 p6 p7 : Close.State → HS.State
p1 owner = at pre1 nothing owner
p2 owner = at pre2 nothing owner
p3 owner = at E.beforeSelect nothing owner
p4 owner = at E.beforeFork nothing owner
p5 owner = at E.forked (just HS.maskedSetup) owner
p6 owner = at pre6 (just HS.maskedSetup) owner
p7 owner = at F.waiting (just HS.maskedSetup) owner
admit-step1 : ∀ owner → HS.step (HS.run (Machine.admissionStep w₀ Server.take)) (at F.start nothing owner) ≡ just (p1 owner)
admit-step1 owner = refl
admit-step2 : ∀ owner → HS.step (HS.run (Machine.admissionStep w₀ Server.countLimit)) (p1 owner) ≡ just (p2 owner)
admit-step2 owner = refl
admit-step3 : ∀ owner → HS.step (HS.run (Machine.admissionStep w₀ Server.allocatePromise)) (p2 owner) ≡ just (p3 owner)
admit-step3 owner = refl
admit-step4 : ∀ owner → HS.step (HS.run (Machine.admissionStep w₀ Server.chooseEntry)) (p3 owner) ≡ just (p4 owner)
admit-step4 owner = refl
admit-step5 : ∀ owner → HS.step (HS.run (Machine.admissionStep w₀ Server.fork)) (p4 owner) ≡ just (p5 owner)
admit-step5 owner = refl
admit-step6 : ∀ owner → HS.step (HS.run (Machine.admissionStep w₀ Server.putMapBack)) (p5 owner) ≡ just (p6 owner)
admit-step6 owner = refl
admit-step7 : ∀ owner → HS.step (HS.run (Machine.admissionStep w₀ Server.readCounters)) (p6 owner) ≡ just (p7 owner)
admit-step7 owner = refl
admit-path : ∀ owner → HS.Executes (at F.start nothing owner) (map HS.run F.admit) (p7 owner)
admit-path owner = HS.next (admit-step1 owner) (HS.next (admit-step2 owner)
  (HS.next (admit-step3 owner) (HS.next (admit-step4 owner) (HS.next (admit-step5 owner)
  (HS.next (admit-step6 owner) (HS.next (admit-step7 owner) HS.done))))))

-- Direct snapshots keep each accepted transition a small source computation.
ownerCaptured ownerRead ownerSending ownerReceived ownerWaiting ownerClosed : Close.State
ownerCaptured = Close.shutdownState Close.reading ((ident 0) ∷ []) ((ident 0) ∷ []) []
ownerRead = Close.shutdownState (Close.sendReady (ident 0) child₀) ((ident 0) ∷ []) [] []
ownerSending = record ownerRead { phase = Close.awaitDelivery (ident 0) child₀ }
ownerReceived = Close.shutdownState Close.reading ((ident 0) ∷ []) [] (child₀ ∷ [])
ownerWaiting = record ownerReceived { phase = Close.awaitResults }
ownerClosed = record ownerWaiting { phase = Close.closed }
h7 h8 h9 h10 h11 h12 h13 h14 h15 : HS.State
h7 = p7 Close.initialState
h8 = at F.waiting (just HS.handshaking) Close.initialState
h9 = at F.waiting (just HS.handshaking) ownerCaptured
h10 = at F.waiting (just HS.handshaking) ownerRead
h11 = at F.waiting (just HS.handshaking) ownerSending
h12 = at F.waiting (just (HS.caughtCancellation err)) ownerReceived
-- Source HandlerError SomeException is classified as protocolViolation by
-- classifyHandlerError; this is not a negotiation-failure result projection.
publishedCaught : Machine.Configuration
publishedCaught = record F.waiting { world = record (Machine.world F.waiting)
  { handshakeResults = ((ident 0) , S.handlerError S.protocolViolation err) ∷ [] } }
h13 = at publishedCaught (just (HS.cancellationPublished err)) ownerReceived
h14 = at publishedCaught (just (HS.bodyExited err)) ownerReceived
cleanupSource : S.CMStore → S.SocketOwner → S.CleanupPC → Machine.Configuration
cleanupSource cm socketOwner pc = record publishedCaught { world = record (Machine.world publishedCaught)
  { cm = cm; sockets = put (ident 0) socketOwner (S.sockets (Machine.world publishedCaught))
  ; cleanups = (child₀ , pc) ∷ [] } }
cleanupEntered : Machine.Configuration
cleanupEntered = cleanupSource (S.cm (Machine.world publishedCaught)) (S.handling child₀) S.cleanupAcquire
h15 = at cleanupEntered (just (HS.finalizing err)) ownerReceived
enter-unmasked-handshake : HS.step (HS.enterHandshake child₀) h7 ≡ just h8
enter-unmasked-handshake = refl
cm-captures-real-fork : HS.step (HS.shutdownStep Close.captureSnapshot) h8 ≡ just h9
cm-captures-real-fork = refl
cm-late-read : HS.step (HS.shutdownStep Close.readEntry) h9 ≡ just h10
cm-late-read = refl
cm-requests-delivery : HS.step (HS.shutdownStep Close.requestCancellation) h10 ≡ just h11
cm-requests-delivery = refl
handshake-delivery-acknowledged : HS.step (HS.deliverShutdownHandshake err) h11 ≡ just h12
handshake-delivery-acknowledged = refl
receipt-does-not-publish-promise : S.handshakeResults (Machine.world (HS.source h12)) ≡ []
receipt-does-not-publish-promise = refl
actual-catch-publishes : HS.step (HS.publishCaught child₀) h12 ≡ just h13
actual-catch-publishes = refl
actual-catch-rethrows : HS.step (HS.rethrowCaught child₀) h13 ≡ just h14
actual-catch-rethrows = refl
actual-finalizer-entry : HS.step (HS.enterFinalizer child₀) h14 ≡ just h15
actual-finalizer-entry = refl
no-result-before-cleanup : HS.step (HS.publishAsyncResult child₀) h14 ≡ nothing
no-result-before-cleanup = refl
no-raw-handler-exit-bypass : HS.step (HS.run (Machine.handlerExit child₀)) h7 ≡ nothing
no-raw-handler-exit-bypass = refl
no-raw-publication-bypass : HS.step (HS.run (Machine.handlerPublication child₀ (S.handlerError S.protocolViolation err) Machine.resultWritten)) h12 ≡ nothing
no-raw-publication-bypass = refl
no-raw-cleanup-bypass : HS.step (HS.run (Machine.cleanupStep child₀ Cleanup.takeCleanupMap)) h15 ≡ nothing
no-raw-cleanup-bypass = refl
no-raw-lifecycle-bypass : HS.step (HS.run (Machine.handlerStep child₀ (Life.attach err))) h7 ≡ nothing
no-raw-lifecycle-bypass = refl
wrong-worker-refused : HS.step (HS.deliverHandshakeCancellation (ident 99) err) h8 ≡ nothing
wrong-worker-refused = refl
no-result-at-receipt : HS.resultReady child₀ h12 ≡ false
no-result-at-receipt = refl
no-result-at-promise : HS.resultReady child₀ h13 ≡ false
no-result-at-promise = refl
earlyWaitReceived earlyWaitPublished : HS.State
earlyWaitReceived = at F.waiting (just (HS.caughtCancellation err)) ownerWaiting
earlyWaitPublished = at publishedCaught (just (HS.cancellationPublished err)) ownerWaiting
actual-early-collective-wait : HS.step (HS.shutdownStep Close.finishTraversal) h12 ≡ just earlyWaitReceived
actual-early-collective-wait = refl
receipt-cannot-close-cm : HS.step (HS.shutdownStep Close.finishClose) earlyWaitReceived ≡ nothing
receipt-cannot-close-cm = refl
promise-cannot-close-cm : HS.step (HS.shutdownStep Close.finishClose) earlyWaitPublished ≡ nothing
promise-cannot-close-cm = refl

-- Real unnegotiated cleanup writes: terminate/purge while owning the map,
-- close the captured socket, publish the map and trace counters.
terminatedHeap : S.EntryHeap
terminatedHeap = ((ident 0) , S.terminated nothing) ∷ []
source16 source17 source18 source19 source20 : Machine.Configuration
source16 = cleanupSource (record (S.cm (Machine.world publishedCaught)) { mapCell = S.taken child₀ })
  (S.handling child₀) (S.cleanupSelect F.childLease)
source17 = cleanupSource (S.cmStore (S.taken child₀) terminatedHeap 1)
  (S.handling child₀) (S.cleanupClose F.childLease [] S.countImmediately)
source18 = cleanupSource (S.cmStore (S.taken child₀) terminatedHeap 1)
  S.closed (S.cleanupPublish F.childLease [] S.countImmediately)
source19 = cleanupSource (S.cmStore (S.full []) terminatedHeap 1) S.closed (S.cleanupCount S.cleanupNormal)
source20 = cleanupSource (S.cmStore (S.full []) terminatedHeap 1) S.closed (S.cleanupDone S.cleanupNormal)
h16 h17 h18 h19 h20 h21 h22 h23 h24 : HS.State
h16 = at source16 (just (HS.finalizing err)) ownerReceived
h17 = at source17 (just (HS.finalizing err)) ownerReceived
h18 = at source18 (just (HS.finalizing err)) ownerReceived
h19 = at source19 (just (HS.finalizing err)) ownerReceived
h20 = at source20 (just (HS.finalizing err)) ownerReceived
h21 = at source20 (just (HS.cleanupComplete err S.cleanupNormal)) ownerReceived
h22 = at source20 (just (HS.resultAvailable err S.cleanupNormal)) ownerReceived
h23 = at source20 (just (HS.resultAvailable err S.cleanupNormal)) ownerWaiting
h24 = at source20 (just (HS.resultAvailable err S.cleanupNormal)) ownerClosed
completion-step16 : HS.step (HS.cleanup child₀ Cleanup.takeCleanupMap) h15 ≡ just h16
completion-step16 = refl
completion-step17 : HS.step (HS.cleanup child₀ Cleanup.selectCleanupEntry) h16 ≡ just h17
completion-step17 = refl
completion-step18 : HS.step (HS.cleanup child₀ Cleanup.closeHandlerSocket) h17 ≡ just h18
completion-step18 = refl
completion-step19 : HS.step (HS.cleanup child₀ Cleanup.publishCleanupMap) h18 ≡ just h19
completion-step19 = refl
completion-step20 : HS.step (HS.cleanup child₀ Cleanup.readCleanupCounters) h19 ≡ just h20
completion-step20 = refl
completion-step21 : HS.step (HS.finishCleanup child₀) h20 ≡ just h21
completion-step21 = refl
completion-step22 : HS.step (HS.publishAsyncResult child₀) h21 ≡ just h22
completion-step22 = refl
completion-step23 : HS.step (HS.shutdownStep Close.finishTraversal) h22 ≡ just h23
completion-step23 = refl
completion-step24 : HS.step (HS.shutdownStep Close.finishClose) h23 ≡ just h24
completion-step24 = refl
cleanup-done-is-not-async-result : HS.resultReady child₀ h21 ≡ false
cleanup-done-is-not-async-result = refl
actual-socket-closed : lookup (ident 0) (S.sockets (Machine.world (HS.source h24))) ≡ just S.closed
actual-socket-closed = refl
actual-map-purged : S.mapCell (S.cm (Machine.world (HS.source h24))) ≡ S.full []
actual-map-purged = refl
actual-entry-terminated : lookup (ident 0) (S.entries (S.cm (Machine.world (HS.source h24)))) ≡ just (S.terminated nothing)
actual-entry-terminated = refl

completionActions : List HS.Action
completionActions = HS.enterHandshake child₀ ∷ HS.shutdownStep Close.captureSnapshot ∷
  HS.shutdownStep Close.readEntry ∷ HS.shutdownStep Close.requestCancellation ∷
  HS.deliverShutdownHandshake err ∷ HS.publishCaught child₀ ∷ HS.rethrowCaught child₀ ∷
  HS.enterFinalizer child₀ ∷ HS.cleanup child₀ Cleanup.takeCleanupMap ∷
  HS.cleanup child₀ Cleanup.selectCleanupEntry ∷ HS.cleanup child₀ Cleanup.closeHandlerSocket ∷
  HS.cleanup child₀ Cleanup.publishCleanupMap ∷ HS.cleanup child₀ Cleanup.readCleanupCounters ∷
  HS.finishCleanup child₀ ∷ HS.publishAsyncResult child₀ ∷
  HS.shutdownStep Close.finishTraversal ∷ HS.shutdownStep Close.finishClose ∷ []
completion-path : HS.Executes h7 completionActions h24
completion-path = HS.next enter-unmasked-handshake (HS.next cm-captures-real-fork
  (HS.next cm-late-read (HS.next cm-requests-delivery (HS.next handshake-delivery-acknowledged
  (HS.next actual-catch-publishes (HS.next actual-catch-rethrows (HS.next actual-finalizer-entry
  (HS.next completion-step16 (HS.next completion-step17 (HS.next completion-step18
  (HS.next completion-step19 (HS.next completion-step20 (HS.next completion-step21
  (HS.next completion-step22 (HS.next completion-step23 (HS.next completion-step24 HS.done))))))))))))))))
append : ∀ {s as t bs u} → HS.Executes s as t → HS.Executes t bs u → HS.Executes s (as ++ bs) u
append HS.done right = right
append (HS.next eq left) right = HS.next eq (append left right)
abstract
  initialized-handshake-cancel-close : HS.Executes h₀ (map HS.run F.admit ++ completionActions) h24
  initialized-handshake-cancel-close = append (admit-path Close.initialState) completion-path

-- Setup is masked outside the restored handshake catch. A separately observed
-- interruptible setup operation permits cancellation without a catch publication.
setupPending setupExited : HS.State
setupPending = at F.waiting (just HS.maskedSetup) ownerSending
setupExited = at F.waiting (just (HS.bodyExited err)) ownerReceived
setup-is-not-handshake-catch : HS.step (HS.deliverShutdownHandshake err) setupPending ≡ nothing
setup-is-not-handshake-catch = refl
observed-blocking-setup-delivery : HS.step (HS.deliverShutdownBlockedSetup err) setupPending ≡ just setupExited
observed-blocking-setup-delivery = refl
setup-does-not-publish-promise : S.handshakeResults (Machine.world (HS.source setupExited)) ≡ []
setup-does-not-publish-promise = refl
setup-cannot-invent-catch-publication : HS.step (HS.publishCaught child₀) setupExited ≡ nothing
setup-cannot-invent-catch-publication = refl
preexisting-heap-is-not-initialized-registry : HS.initial F.waiting ≡ nothing
preexisting-heap-is-not-initialized-registry = refl
no-uncoupled-shutdown-receipt : HS.step (HS.shutdownStep Close.acknowledgeDelivery) h11 ≡ nothing
no-uncoupled-shutdown-receipt = refl

-- A throwing socket close restores the captured map; the committed entry write
-- and uncertain socket outcome persist. Async completion records that outcome.
failedSource restoredSource : Machine.Configuration
failedSource = cleanupSource (S.cmStore (S.taken child₀) terminatedHeap 1)
  (S.closeUncertain closeErr) (S.cleanupRestore F.childLease closeErr)
restoredSource = cleanupSource (S.cmStore (S.full F.binding) terminatedHeap 1)
  (S.closeUncertain closeErr) (S.cleanupDone (S.cleanupError closeErr))
closeFailed closeRestored closeFinished closeResult : HS.State
closeFailed = at failedSource (just (HS.finalizing err)) ownerReceived
closeRestored = at restoredSource (just (HS.finalizing err)) ownerReceived
closeFinished = at restoredSource (just (HS.cleanupComplete err (S.cleanupError closeErr))) ownerReceived
closeResult = at restoredSource (just (HS.resultAvailable err (S.cleanupError closeErr))) ownerReceived
actual-close-fails : HS.step (HS.cleanup child₀ (Cleanup.failSocketClose closeErr)) h17 ≡ just closeFailed
actual-close-fails = refl
actual-map-restored-on-error : HS.step (HS.cleanup child₀ Cleanup.restoreCleanupMap) closeFailed ≡ just closeRestored
actual-map-restored-on-error = refl
close-error-completes-cleanup : HS.step (HS.finishCleanup child₀) closeRestored ≡ just closeFinished
close-error-completes-cleanup = refl
close-error-publishes-async-outcome : HS.step (HS.publishAsyncResult child₀) closeFinished ≡ just closeResult
close-error-publishes-async-outcome = refl
close-error-keeps-uncertain-socket : lookup (ident 0) (S.sockets (Machine.world (HS.source closeResult))) ≡ just (S.closeUncertain closeErr)
close-error-keeps-uncertain-socket = refl
close-error-retains-restored-map : S.mapCell (S.cm (Machine.world (HS.source closeResult))) ≡ S.full F.binding
close-error-retains-restored-map = refl
cleanup-error-overrides-cancellation : HS.effectiveError err (S.cleanupError closeErr) ≡ closeErr
cleanup-error-overrides-cancellation = refl

-- Even this physical adapter's closed empty snapshot does not freeze accepted
-- admissions. The same seven actual steps register a new child afterward.
emptyCaptured emptyWaiting emptyClosed : Close.State
emptyCaptured = Close.shutdownState Close.reading [] [] []
emptyWaiting = Close.shutdownState Close.awaitResults [] [] []
emptyClosed = Close.shutdownState Close.closed [] [] []
empty-capture : HS.step (HS.shutdownStep Close.captureSnapshot) h₀ ≡ just (at F.start nothing emptyCaptured)
empty-capture = refl
empty-traversal : HS.step (HS.shutdownStep Close.finishTraversal) (at F.start nothing emptyCaptured) ≡ just (at F.start nothing emptyWaiting)
empty-traversal = refl
empty-close : HS.step (HS.shutdownStep Close.finishClose) (at F.start nothing emptyWaiting) ≡ just (at F.start nothing emptyClosed)
empty-close = refl
emptyCloseActions : List HS.Action
emptyCloseActions = HS.shutdownStep Close.captureSnapshot ∷ HS.shutdownStep Close.finishTraversal ∷ HS.shutdownStep Close.finishClose ∷ []
empty-close-path : HS.Executes h₀ emptyCloseActions (at F.start nothing emptyClosed)
empty-close-path = HS.next empty-capture (HS.next empty-traversal (HS.next empty-close HS.done))
abstract
  initialized-closed-then-admitted : HS.Executes h₀
    (emptyCloseActions ++ map HS.run F.admit) (p7 emptyClosed)
  initialized-closed-then-admitted = append empty-close-path (admit-path emptyClosed)
late-child-physically-captured : lookup child₀ (HS.threads (p7 emptyClosed)) ≡ just (HS.handlerThread captured HS.maskedSetup)
late-child-physically-captured = refl
late-snapshot-stays-empty : Close.snapshot (HS.shutdown (p7 emptyClosed)) ≡ []
late-snapshot-stays-empty = refl

-- Conditional TIME_WAIT finalizer window: a received exception acknowledges
-- the sender but still runs the captured termination/purge transaction.
term : S.ConnectionState
term = S.terminating key₀ child₀ nothing
waitingTimeSource interruptedTimeSource finalizedTimeSource : Machine.Configuration
waitingTimeSource = cleanupSource (S.cmStore (S.full F.binding) (((ident 0) , term) ∷ []) 1)
  S.closed (S.cleanupWaiting term)
interruptedTimeSource = cleanupSource (S.cmStore (S.full F.binding) (((ident 0) , term) ∷ []) 1)
  S.closed (S.cleanupFinalize term (S.cleanupError closeErr))
finalizedTimeSource = cleanupSource (S.cmStore (S.full []) terminatedHeap 1)
  S.closed (S.cleanupCount (S.cleanupError closeErr))
waitingTime interruptedTime finalizedTime : HS.State
waitingTime = at waitingTimeSource (just (HS.finalizing err)) ownerSending
interruptedTime = at interruptedTimeSource (just (HS.finalizing err)) ownerReceived
finalizedTime = at finalizedTimeSource (just (HS.finalizing err)) ownerReceived
actual-time-wait-delivery : HS.step (HS.deliverShutdownTimeWait closeErr) waitingTime ≡ just interruptedTime
actual-time-wait-delivery = refl
interrupted-wait-still-needs-final-transaction : HS.step (HS.finishCleanup child₀) interruptedTime ≡ nothing
interrupted-wait-still-needs-final-transaction = refl
actual-time-wait-final-transaction : HS.step (HS.cleanup child₀ Cleanup.finishTimeWait) interruptedTime ≡ just finalizedTime
actual-time-wait-final-transaction = refl
interrupted-wait-map-purged : S.mapCell (S.cm (Machine.world (HS.source finalizedTime))) ≡ S.full []
interrupted-wait-map-purged = refl
interrupted-wait-entry-terminated : lookup (ident 0) (S.entries (S.cm (Machine.world (HS.source finalizedTime)))) ≡ just (S.terminated nothing)
interrupted-wait-entry-terminated = refl
interrupted-wait-does-not-republish-promise : S.handshakeResults (Machine.world (HS.source interruptedTime)) ≡ S.handshakeResults (Machine.world publishedCaught)
interrupted-wait-does-not-republish-promise = refl

-- The real fork can run its child before the masked parent republishes the CM
-- map. Child finally cannot acquire that map until the parent releases it.
forkBodyExited forkFinalizing forkMapPublished : HS.State
forkBodyExited = at E.forked (just (HS.bodyExited err)) Close.initialState
forkFinalizing = at (record E.forked { world = record (Machine.world E.forked)
  { cleanups = (child₀ , S.cleanupAcquire) ∷ [] } }) (just (HS.finalizing err)) Close.initialState
forkMapPublished = at (record pre6 { world = record (Machine.world pre6)
  { cleanups = (child₀ , S.cleanupAcquire) ∷ [] } }) (just (HS.finalizing err)) Close.initialState
actual-early-child-cancel : HS.step (HS.deliverBlockedSetupCancellation child₀ err) (p5 Close.initialState) ≡ just forkBodyExited
actual-early-child-cancel = refl
actual-early-finalizer-entry : HS.step (HS.enterFinalizer child₀) forkBodyExited ≡ just forkFinalizing
actual-early-finalizer-entry = refl
child-finalizer-blocks-on-parent-map : HS.step (HS.cleanup child₀ Cleanup.takeCleanupMap) forkFinalizing ≡ nothing
child-finalizer-blocks-on-parent-map = refl
parent-can-publish-during-child-finalizer : HS.step (HS.run (Machine.admissionStep w₀ Server.putMapBack)) forkFinalizing ≡ just forkMapPublished
parent-can-publish-during-child-finalizer = refl

-- The admission consumer may run between the catch publication and rethrow.
-- Generic HandlerError's protocolViolation classification removes this binding
-- and writes Terminated, so it does not create a TIME_WAIT obligation.
import ConnectionManagement.Rules.Handshake as Handshake
caughtReadSource caughtCommitSource : Machine.Configuration
caughtReadSource = record publishedCaught { world = record (Machine.world publishedCaught)
  { admissions = F.requests (S.commitHandshake (ident 0) (S.handlerError S.protocolViolation err)) } }
caughtCommitSource = record publishedCaught { world = record (Machine.world publishedCaught)
  { admissions = F.requests (S.countHandshake (S.disconnected (S.handshakeError S.protocolViolation err)))
  ; cm = S.cmStore (S.full []) (((ident 0) , S.terminated (just err)) ∷ []) 1 } }
caughtRead caughtCommitted : HS.State
caughtRead = at caughtReadSource (just (HS.cancellationPublished err)) ownerReceived
caughtCommitted = at caughtCommitSource (just (HS.cancellationPublished err)) ownerReceived
actual-consumer-reads-caught-error : HS.step (HS.run (Machine.handshakeStep w₀ Handshake.readResult)) h13 ≡ just caughtRead
actual-consumer-reads-caught-error = refl
actual-consumer-commits-protocol-error : HS.step (HS.run (Machine.handshakeStep w₀ Handshake.commitResult)) caughtRead ≡ just caughtCommitted
actual-consumer-commits-protocol-error = refl
caught-consumer-path : HS.Executes h13
  (HS.run (Machine.handshakeStep w₀ Handshake.readResult) ∷ HS.run (Machine.handshakeStep w₀ Handshake.commitResult) ∷ []) caughtCommitted
caught-consumer-path = HS.next actual-consumer-reads-caught-error (HS.next actual-consumer-commits-protocol-error HS.done)
caught-error-consumer-removes-binding : S.mapCell (S.cm (Machine.world (HS.source caughtCommitted))) ≡ S.full []
caught-error-consumer-removes-binding = refl
caught-error-consumer-writes-terminated : lookup (ident 0) (S.entries (S.cm (Machine.world (HS.source caughtCommitted)))) ≡ just (S.terminated (just err))
caught-error-consumer-writes-terminated = refl


-- Instantiate the generic projection and physical-oracle certificate with the
-- actual initialized path, retaining real dispatcher writes and cleanup effects.
import ConnectionManagement.Properties.HandlerSupervision as Facts
open import Data.Product using (_×_; proj₂)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import Data.List.Relation.Unary.All as All
completion-certificate : Close.remaining ownerClosed ≡ [] × Facts.PhysicalWait ownerClosed
completion-certificate = Facts.closed-from-initial {c = F.start}
  actual-empty-initializer initialized-handshake-cancel-close refl
completion-source-path : Facts.MTrace F.start source20
completion-source-path = Facts.machine (Facts.exec-projects initialized-handshake-cancel-close)
completion-supply-bounds : SupplyBounds (Machine.world source20)
completion-supply-bounds = Facts.supply-preserves (All.[] , All.[])
  initialized-handshake-cancel-close

completion-publication-checkpoint : Facts.ResultPublication child₀ h21 h22
completion-publication-checkpoint = Facts.publication-observation child₀ h21 completion-step22
failed-publication-checkpoint : Facts.ResultPublication child₀ closeFinished closeResult
failed-publication-checkpoint = Facts.publication-observation child₀ closeFinished
  close-error-publishes-async-outcome
