{-# OPTIONS --guardedness #-}

-- Initialized outbound physical creation and pre-handshake cancellation. These
-- are standalone source-model interleavings; the surrounding diffusion caller
-- joins are not inferred from a CM snapshot close.
module ConnectionManagement.Negative.OutboundHandlerSupervision where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.OutboundHandlerSupervision as X
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as M
import ConnectionManagement.State as S
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.CSP.OutboundAdmission as Fixture
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.Negative.HandlerSupervision as Inbound
open import ConnectionManagement.Scenarios.Admission using (key₀; w₀; w₁; child₀)

err : ErrorId
err = errorId 9
captured : S.HandlerStart
captured = S.handlerStart (ident 0) Fixture.sock (ident 0) key₀
at : O.Configuration → Maybe H.Phase → Close.State → X.State
at c nothing owner = X.supervised c [] owner
at c (just phase) owner = X.supervised c ((Fixture.child , H.handlerThread captured phase) ∷ []) owner
p₀ : X.State
p₀ = at (O.initial F.start) nothing Close.initialState
actual-initializer : X.initial (O.initial F.start) ≡ just p₀
actual-initializer = refl
p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : X.State
p1 = at Fixture.begun nothing Close.initialState
p2 = at (Fixture.at (A.count (A.allocatePromise (ident 0))) Fixture.reserved) nothing Close.initialState
p3 = at (Fixture.at (A.allocatePromise (ident 0)) Fixture.reserved) nothing Close.initialState
p4 = at (Fixture.at (A.openSocket (ident 0) (ident 0)) Fixture.promised) nothing Close.initialState
p5 = at (Fixture.at (A.configureSocket (ident 0) (ident 0)) Fixture.opened) nothing Close.initialState
p6 = at (Fixture.at (A.connectSocket (ident 0) (ident 0)) Fixture.opened) nothing Close.initialState
p7 = at (Fixture.at (A.localAddress (ident 0) (ident 0)) Fixture.opened) nothing Close.initialState
p8 = at (Fixture.at (A.updateAddress (ident 0) (ident 0) key₀) Fixture.opened) nothing Close.initialState
p9 = at (Fixture.at (A.forkHandler (ident 0) (ident 0) key₀) Fixture.addressed) nothing Close.initialState
p10 = at (Fixture.at (A.connectedCommit (ident 0) (ident 0) key₀) Fixture.forked) (just H.maskedSetup) Close.initialState
prefix-step1 : X.step (X.outbound (O.beginAcquire Fixture.caller Fixture.req)) p₀ ≡ just p1
prefix-step1 = refl
prefix-step2 : X.step (X.outbound (O.acquire Fixture.caller (A.select nothing))) p1 ≡ just p2
prefix-step2 = refl
prefix-step3 : X.step (X.outbound (O.acquire Fixture.caller A.readCounters)) p2 ≡ just p3
prefix-step3 = refl
prefix-step4 : X.step (X.outbound (O.acquire Fixture.caller A.newPromise)) p3 ≡ just p4
prefix-step4 = refl
prefix-step5 : X.step (X.outbound (O.acquire Fixture.caller A.openOK)) p4 ≡ just p5
prefix-step5 = refl
prefix-step6 : X.step (X.outbound (O.acquire Fixture.caller A.configureOK)) p5 ≡ just p6
prefix-step6 = refl
prefix-step7 : X.step (X.outbound (O.acquire Fixture.caller A.connectOK)) p6 ≡ just p7
prefix-step7 = refl
prefix-step8 : X.step (X.outbound (O.acquire Fixture.caller (A.gotLocal (local key₀)))) p7 ≡ just p8
prefix-step8 = refl
prefix-step9 : X.step (X.outbound (O.acquire Fixture.caller A.updateLocalAddress)) p8 ≡ just p9
prefix-step9 = refl
prefix-step10 : X.step (X.outbound (O.acquire Fixture.caller A.forkOK)) p9 ≡ just p10
prefix-step10 = refl
prefix : List X.Action
prefix = (X.outbound (O.beginAcquire Fixture.caller Fixture.req)) ∷ (X.outbound (O.acquire Fixture.caller (A.select nothing))) ∷ (X.outbound (O.acquire Fixture.caller A.readCounters)) ∷ (X.outbound (O.acquire Fixture.caller A.newPromise)) ∷ (X.outbound (O.acquire Fixture.caller A.openOK)) ∷ (X.outbound (O.acquire Fixture.caller A.configureOK)) ∷ (X.outbound (O.acquire Fixture.caller A.connectOK)) ∷ (X.outbound (O.acquire Fixture.caller (A.gotLocal (local key₀)))) ∷ (X.outbound (O.acquire Fixture.caller A.updateLocalAddress)) ∷ (X.outbound (O.acquire Fixture.caller A.forkOK)) ∷ []
abstract
  initialized-fork : X.Executes p₀ prefix p10
  initialized-fork = X.next prefix-step1 (X.next prefix-step2 (X.next prefix-step3 (X.next prefix-step4 (X.next prefix-step5 (X.next prefix-step6 (X.next prefix-step7 (X.next prefix-step8 (X.next prefix-step9 (X.next prefix-step10 (X.done))))))))))

-- Physical creation precedes Connected's separate STM write. The child can
-- enter the restored handshake while its entry is still ReservedOutbound.
p11 p12 : X.State
p11 = at (X.source p10) (just H.handshaking) Close.initialState
connectedSource : O.Configuration
connectedSource = Fixture.at (A.count Fixture.wait) Fixture.connected
p12 = at connectedSource (just H.handshaking) Close.initialState
child-runs-before-connected : X.step (X.handler (H.enterHandshake Fixture.child)) p10 ≡ just p11
child-runs-before-connected = refl
parent-commits-after-child-runs : X.step (X.outbound (O.acquire Fixture.caller A.commitConnected)) p11 ≡ just p12
parent-commits-after-child-runs = refl
physical-fork-captured : lookup Fixture.child (X.threads p10) ≡ just (H.handlerThread captured H.maskedSetup)
physical-fork-captured = refl
entry-not-yet-connected : lookup (ident 0) (S.entries (S.cm (M.world (O.core (X.source p10))))) ≡ just S.reservedOutbound
entry-not-yet-connected = refl
reserved-entry-has-no-thread-projection : Close.getConnThread S.reservedOutbound ≡ nothing
reserved-entry-has-no-thread-projection = refl
old-initializer-cannot-adopt-fork : H.initial (O.core (X.source p10)) ≡ nothing
old-initializer-cannot-adopt-fork = refl
new-initializer-cannot-adopt-fork : X.initial (X.source p10) ≡ nothing
new-initializer-cannot-adopt-fork = refl

ownerCaptured ownerRead ownerSending ownerReceived ownerWaiting ownerClosed : Close.State
ownerCaptured = Close.shutdownState Close.reading ((ident 0) ∷ []) ((ident 0) ∷ []) []
ownerRead = Close.shutdownState (Close.sendReady (ident 0) Fixture.child) ((ident 0) ∷ []) [] []
ownerSending = record ownerRead { phase = Close.awaitDelivery (ident 0) Fixture.child }
ownerReceived = Close.shutdownState Close.reading ((ident 0) ∷ []) [] (Fixture.child ∷ [])
ownerWaiting = record ownerReceived { phase = Close.awaitResults }
ownerClosed = record ownerWaiting { phase = Close.closed }
p13 p14 p15 p16 p17 p18 p19 : X.State
p13 = at connectedSource (just H.handshaking) ownerCaptured
p14 = at connectedSource (just H.handshaking) ownerRead
p15 = at connectedSource (just H.handshaking) ownerSending
p16 = at connectedSource (just (H.caughtCancellation err)) ownerReceived
publishedSource : O.Configuration
publishedSource = record connectedSource { core = M.replaceWorld (O.core connectedSource)
  (record Fixture.connected { handshakeResults = ((ident 0) , S.handlerError S.protocolViolation err) ∷ [] }) }
p17 = at publishedSource (just (H.cancellationPublished err)) ownerReceived
p18 = at publishedSource (just (H.bodyExited err)) ownerReceived
handlerLease : S.Lease
handlerLease = S.lease Fixture.child F.binding
cleanupSource : S.CMStore → S.SocketOwner → S.CleanupPC → O.Configuration
cleanupSource cm socketOwner pc = record publishedSource { core = M.replaceWorld (O.core publishedSource)
  (record (M.world (O.core publishedSource))
    { cm = cm; sockets = put Fixture.sock socketOwner (S.sockets (M.world (O.core publishedSource)))
    ; cleanups = (Fixture.child , pc) ∷ [] }) }
source19 source20 source21 source22 source23 source24 : O.Configuration
source19 = cleanupSource (S.cm Fixture.connected) (S.handling Fixture.child) S.cleanupAcquire
source20 = cleanupSource (record (S.cm Fixture.connected) { mapCell = S.taken Fixture.child })
  (S.handling Fixture.child) (S.cleanupSelect handlerLease)
terminatedHeap : S.EntryHeap
terminatedHeap = ((ident 0) , S.terminated nothing) ∷ []
source21 = cleanupSource (S.cmStore (S.taken Fixture.child) terminatedHeap 1)
  (S.handling Fixture.child) (S.cleanupClose handlerLease [] S.countImmediately)
source22 = cleanupSource (S.cmStore (S.taken Fixture.child) terminatedHeap 1)
  S.closed (S.cleanupPublish handlerLease [] S.countImmediately)
source23 = cleanupSource (S.cmStore (S.full []) terminatedHeap 1) S.closed (S.cleanupCount S.cleanupNormal)
source24 = cleanupSource (S.cmStore (S.full []) terminatedHeap 1) S.closed (S.cleanupDone S.cleanupNormal)
p19 = at source19 (just (H.finalizing err)) ownerReceived
p20 p21 p22 p23 p24 p25 p26 p27 p28 : X.State
p20 = at source20 (just (H.finalizing err)) ownerReceived
p21 = at source21 (just (H.finalizing err)) ownerReceived
p22 = at source22 (just (H.finalizing err)) ownerReceived
p23 = at source23 (just (H.finalizing err)) ownerReceived
p24 = at source24 (just (H.finalizing err)) ownerReceived
p25 = at source24 (just (H.cleanupComplete err S.cleanupNormal)) ownerReceived
p26 = at source24 (just (H.resultAvailable err S.cleanupNormal)) ownerReceived
p27 = at source24 (just (H.resultAvailable err S.cleanupNormal)) ownerWaiting
p28 = at source24 (just (H.resultAvailable err S.cleanupNormal)) ownerClosed
close-step13 : X.step (X.handler (H.shutdownStep Close.captureSnapshot)) p12 ≡ just p13
close-step13 = refl
close-step14 : X.step (X.handler (H.shutdownStep Close.readEntry)) p13 ≡ just p14
close-step14 = refl
close-step15 : X.step (X.handler (H.shutdownStep Close.requestCancellation)) p14 ≡ just p15
close-step15 = refl
close-step16 : X.step (X.handler (H.deliverShutdownHandshake err)) p15 ≡ just p16
close-step16 = refl
close-step17 : X.step (X.handler (H.publishCaught Fixture.child)) p16 ≡ just p17
close-step17 = refl
close-step18 : X.step (X.handler (H.rethrowCaught Fixture.child)) p17 ≡ just p18
close-step18 = refl
close-step19 : X.step (X.handler (H.enterFinalizer Fixture.child)) p18 ≡ just p19
close-step19 = refl
close-step20 : X.step (X.handler (H.cleanup Fixture.child Cleanup.takeCleanupMap)) p19 ≡ just p20
close-step20 = refl
close-step21 : X.step (X.handler (H.cleanup Fixture.child Cleanup.selectCleanupEntry)) p20 ≡ just p21
close-step21 = refl
close-step22 : X.step (X.handler (H.cleanup Fixture.child Cleanup.closeHandlerSocket)) p21 ≡ just p22
close-step22 = refl
close-step23 : X.step (X.handler (H.cleanup Fixture.child Cleanup.publishCleanupMap)) p22 ≡ just p23
close-step23 = refl
close-step24 : X.step (X.handler (H.cleanup Fixture.child Cleanup.readCleanupCounters)) p23 ≡ just p24
close-step24 = refl
close-step25 : X.step (X.handler (H.finishCleanup Fixture.child)) p24 ≡ just p25
close-step25 = refl
close-step26 : X.step (X.handler (H.publishAsyncResult Fixture.child)) p25 ≡ just p26
close-step26 = refl
close-step27 : X.step (X.handler (H.shutdownStep Close.finishTraversal)) p26 ≡ just p27
close-step27 = refl
close-step28 : X.step (X.handler (H.shutdownStep Close.finishClose)) p27 ≡ just p28
close-step28 = refl
completionActions : List X.Action
completionActions = X.handler (H.enterHandshake Fixture.child) ∷ X.outbound (O.acquire Fixture.caller A.commitConnected) ∷ (X.handler (H.shutdownStep Close.captureSnapshot)) ∷ (X.handler (H.shutdownStep Close.readEntry)) ∷ (X.handler (H.shutdownStep Close.requestCancellation)) ∷ (X.handler (H.deliverShutdownHandshake err)) ∷ (X.handler (H.publishCaught Fixture.child)) ∷ (X.handler (H.rethrowCaught Fixture.child)) ∷ (X.handler (H.enterFinalizer Fixture.child)) ∷ (X.handler (H.cleanup Fixture.child Cleanup.takeCleanupMap)) ∷ (X.handler (H.cleanup Fixture.child Cleanup.selectCleanupEntry)) ∷ (X.handler (H.cleanup Fixture.child Cleanup.closeHandlerSocket)) ∷ (X.handler (H.cleanup Fixture.child Cleanup.publishCleanupMap)) ∷ (X.handler (H.cleanup Fixture.child Cleanup.readCleanupCounters)) ∷ (X.handler (H.finishCleanup Fixture.child)) ∷ (X.handler (H.publishAsyncResult Fixture.child)) ∷ (X.handler (H.shutdownStep Close.finishTraversal)) ∷ (X.handler (H.shutdownStep Close.finishClose)) ∷ []
completion-path : X.Executes p10 completionActions p28
completion-path = X.next child-runs-before-connected (X.next parent-commits-after-child-runs (X.next close-step13 (X.next close-step14 (X.next close-step15 (X.next close-step16 (X.next close-step17 (X.next close-step18 (X.next close-step19 (X.next close-step20 (X.next close-step21 (X.next close-step22 (X.next close-step23 (X.next close-step24 (X.next close-step25 (X.next close-step26 (X.next close-step27 (X.next close-step28 (X.done))))))))))))))))))
append : ∀ {s as t bs u} → X.Executes s as t → X.Executes t bs u → X.Executes s (as ++ bs) u
append X.done right = right
append (X.next eq left) right = X.next eq (append left right)
abstract
  initialized-outbound-handler-close : X.Executes p₀ (prefix ++ completionActions) p28
  initialized-outbound-handler-close = append initialized-fork completion-path
actual-outbound-socket-closed : lookup Fixture.sock (S.sockets (M.world (O.core (X.source p28)))) ≡ just S.closed
actual-outbound-socket-closed = refl
actual-outbound-map-purged : S.mapCell (S.cm (M.world (O.core (X.source p28)))) ≡ S.full []
actual-outbound-map-purged = refl
caller-retains-captured-await : O.acquiring (X.source p28) ≡ (Fixture.caller , A.frame Fixture.req (A.count Fixture.wait)) ∷ []
caller-retains-captured-await = refl
no-inbound-handler-exit-bypass : X.step (X.outbound (O.inbound (M.handlerExit Fixture.child))) p12 ≡ nothing
no-inbound-handler-exit-bypass = refl
no-inbound-publication-bypass : X.step (X.outbound (O.inbound (M.handlerPublication Fixture.child (S.handlerError S.protocolViolation err) M.resultWritten))) p16 ≡ nothing
no-inbound-publication-bypass = refl
physical-worker-cannot-become-caller : X.step (X.outbound (O.beginAcquire Fixture.child Fixture.req)) p10 ≡ nothing
physical-worker-cannot-become-caller = refl
physical-worker-cannot-become-release-caller : X.step (X.outbound (O.beginRelease Fixture.child key₀)) p10 ≡ nothing
physical-worker-cannot-become-release-caller = refl
reused-physical-child-refused : X.step (X.outbound (O.acquire Fixture.caller A.forkOK))
  (record p9 { threads = X.threads p10 }) ≡ nothing
reused-physical-child-refused = refl

-- This pending release is a local interleaving fixture. Its open-machine ack
-- is enabled, but the physical wrapper requires its coupled delivery action.
releaseCaller : WorkerId
releaseCaller = ident 20
pendingRelease : O.Configuration
pendingRelease = record connectedSource { releasing = (releaseCaller ,
  R.frame key₀ (R.delivering Fixture.child (R.complete (R.success nothing))) false) ∷ [] }
raw-release-receipt-enabled : O.advance (O.release releaseCaller (R.cancellationDelivered Fixture.child)) pendingRelease ≡ just
  (record pendingRelease { releasing = (releaseCaller , R.frame key₀ (R.complete (R.success nothing)) false) ∷ [] })
raw-release-receipt-enabled = refl
raw-release-receipt-cannot-bypass-registry : X.step (X.outbound (O.release releaseCaller (R.cancellationDelivered Fixture.child)))
  (at pendingRelease (just H.handshaking) Close.initialState) ≡ nothing
raw-release-receipt-cannot-bypass-registry = refl

-- Initialized local snapshot/fork window. The CM entry projection can miss a
-- physical child before Connected commits. Outer diffusion caller joins may
-- exclude this ordering at their own shutdown boundary; none is asserted here.
skippedOwner skippedWaiting skippedClosed : Close.State
skippedOwner = Close.shutdownState Close.reading ((ident 0) ∷ []) [] []
skippedWaiting = record skippedOwner { phase = Close.awaitResults }
skippedClosed = record skippedWaiting { phase = Close.closed }
s1 s2 s3 s4 : X.State
s1 = at (X.source p10) (just H.maskedSetup) ownerCaptured
s2 = at (X.source p10) (just H.maskedSetup) skippedOwner
s3 = at (X.source p10) (just H.maskedSetup) skippedWaiting
s4 = at (X.source p10) (just H.maskedSetup) skippedClosed
fork-window-snapshot : X.step (X.handler (H.shutdownStep Close.captureSnapshot)) p10 ≡ just s1
fork-window-snapshot = refl
fork-window-read-skips-physical-child : X.step (X.handler (H.shutdownStep Close.readEntry)) s1 ≡ just s2
fork-window-read-skips-physical-child = refl
fork-window-traversal : X.step (X.handler (H.shutdownStep Close.finishTraversal)) s2 ≡ just s3
fork-window-traversal = refl
fork-window-close : X.step (X.handler (H.shutdownStep Close.finishClose)) s3 ≡ just s4
fork-window-close = refl
forkWindowActions : List X.Action
forkWindowActions = X.handler (H.shutdownStep Close.captureSnapshot) ∷
  X.handler (H.shutdownStep Close.readEntry) ∷ X.handler (H.shutdownStep Close.finishTraversal) ∷
  X.handler (H.shutdownStep Close.finishClose) ∷ []
fork-window-path : X.Executes p10 forkWindowActions s4
fork-window-path = X.next fork-window-snapshot (X.next fork-window-read-skips-physical-child
  (X.next fork-window-traversal (X.next fork-window-close X.done)))
abstract
  initialized-cm-snapshot-skips-created-child : X.Executes p₀ (prefix ++ forkWindowActions) s4
  initialized-cm-snapshot-skips-created-child = append initialized-fork fork-window-path
closed-fork-window-retains-live-physical-child : lookup Fixture.child (X.threads s4) ≡ just (H.handlerThread captured H.maskedSetup)
closed-fork-window-retains-live-physical-child = refl

-- Concrete wrapper lifting preserves outbound caller fields across independent
-- inbound source actions; every lifted step checks the wrapper's actual guard.
liftAt : O.Configuration → H.State → X.State
liftAt base h = X.supervised (record base { core = H.source h }) (H.threads h) (H.shutdown h)
lift-step : ∀ base action before after → H.step action before ≡ just after →
  X.handlerAllowed action (liftAt base before) ≡ true →
  X.step (X.handler action) (liftAt base before) ≡ just (liftAt base after)
lift-step base action before after advanced allowed rewrite allowed | advanced = refl
admitLift : ∀ base owner → X.freshChild child₀ (liftAt base (Inbound.p4 owner)) ≡ true →
  X.Executes (liftAt base (Inbound.at F.start nothing owner))
    (map (λ a → X.handler (H.run a)) F.admit) (liftAt base (Inbound.p7 owner))
admitLift base owner fresh = X.next (lift-step base (H.run (M.admissionStep w₀ Server.take)) (Inbound.at F.start nothing owner) (Inbound.p1 owner) (Inbound.admit-step1 owner) refl) (X.next (lift-step base (H.run (M.admissionStep w₀ Server.countLimit)) (Inbound.p1 owner) (Inbound.p2 owner) (Inbound.admit-step2 owner) refl) (X.next (lift-step base (H.run (M.admissionStep w₀ Server.allocatePromise)) (Inbound.p2 owner) (Inbound.p3 owner) (Inbound.admit-step3 owner) refl) (X.next (lift-step base (H.run (M.admissionStep w₀ Server.chooseEntry)) (Inbound.p3 owner) (Inbound.p4 owner) (Inbound.admit-step4 owner) refl) (X.next (lift-step base (H.run (M.admissionStep w₀ Server.fork)) (Inbound.p4 owner) (Inbound.p5 owner) (Inbound.admit-step5 owner) fresh) (X.next (lift-step base (H.run (M.admissionStep w₀ Server.putMapBack)) (Inbound.p5 owner) (Inbound.p6 owner) (Inbound.admit-step6 owner) refl) (X.next (lift-step base (H.run (M.admissionStep w₀ Server.readCounters)) (Inbound.p6 owner) (Inbound.p7 owner) (Inbound.admit-step7 owner) refl) (X.done)))))))
alongsideSource : X.State
alongsideSource = liftAt Fixture.begun (Inbound.p7 Close.initialState)
actual-inbound-alongside-outbound : X.Executes p1
  (map (λ a → X.handler (H.run a)) F.admit) alongsideSource
actual-inbound-alongside-outbound = admitLift Fixture.begun Close.initialState refl
abstract
  initialized-inbound-outbound-interleaving : X.Executes p₀
    (X.outbound (O.beginAcquire Fixture.caller Fixture.req) ∷ map (λ a → X.handler (H.run a)) F.admit) alongsideSource
  initialized-inbound-outbound-interleaving = X.next prefix-step1 actual-inbound-alongside-outbound
inbound-fork-retains-outbound-caller : O.acquiring (X.source alongsideSource) ≡ O.acquiring Fixture.begun
inbound-fork-retains-outbound-caller = refl
inbound-fork-captures-independent-child : lookup child₀ (X.threads alongsideSource) ≡ just (H.handlerThread Inbound.captured H.maskedSetup)
inbound-fork-captures-independent-child = refl

-- Empty coordinator closure also permits later actual admission in this
-- outbound adapter; its initializer does not adopt the resulting handler.
empty1 empty2 empty3 : X.State
empty1 = liftAt (O.initial F.start) (Inbound.at F.start nothing Inbound.emptyCaptured)
empty2 = liftAt (O.initial F.start) (Inbound.at F.start nothing Inbound.emptyWaiting)
empty3 = liftAt (O.initial F.start) (Inbound.at F.start nothing Inbound.emptyClosed)
empty-capture : X.step (X.handler (H.shutdownStep Close.captureSnapshot)) p₀ ≡ just empty1
empty-capture = lift-step (O.initial F.start) (H.shutdownStep Close.captureSnapshot) Inbound.h₀
  (Inbound.at F.start nothing Inbound.emptyCaptured) Inbound.empty-capture refl
empty-traversal : X.step (X.handler (H.shutdownStep Close.finishTraversal)) empty1 ≡ just empty2
empty-traversal = lift-step (O.initial F.start) (H.shutdownStep Close.finishTraversal)
  (Inbound.at F.start nothing Inbound.emptyCaptured) (Inbound.at F.start nothing Inbound.emptyWaiting) Inbound.empty-traversal refl
empty-close : X.step (X.handler (H.shutdownStep Close.finishClose)) empty2 ≡ just empty3
empty-close = lift-step (O.initial F.start) (H.shutdownStep Close.finishClose)
  (Inbound.at F.start nothing Inbound.emptyWaiting) (Inbound.at F.start nothing Inbound.emptyClosed) Inbound.empty-close refl
emptyCloseActions : List X.Action
emptyCloseActions = X.handler (H.shutdownStep Close.captureSnapshot) ∷
  X.handler (H.shutdownStep Close.finishTraversal) ∷ X.handler (H.shutdownStep Close.finishClose) ∷ []
empty-close-path : X.Executes p₀ emptyCloseActions empty3
empty-close-path = X.next empty-capture (X.next empty-traversal (X.next empty-close X.done))
lateSource : X.State
lateSource = liftAt (O.initial F.start) (Inbound.p7 Inbound.emptyClosed)
late-admission : X.Executes empty3 (map (λ a → X.handler (H.run a)) F.admit) lateSource
late-admission = admitLift (O.initial F.start) Inbound.emptyClosed refl
abstract
  initialized-late-admission-after-empty-close : X.Executes p₀
    (emptyCloseActions ++ map (λ a → X.handler (H.run a)) F.admit) lateSource
  initialized-late-admission-after-empty-close = append empty-close-path late-admission
late-physical-child-captured : lookup child₀ (X.threads lateSource) ≡ just (H.handlerThread Inbound.captured H.maskedSetup)
late-physical-child-captured = refl
late-coordinator-snapshot-remains-empty : Close.snapshot (X.shutdown lateSource) ≡ []
late-coordinator-snapshot-remains-empty = refl

-- Generic certificates consume the actual initialized execution, including its
-- outbound shared writers and still-captured awaiting caller continuation.
import ConnectionManagement.Properties.OutboundHandlerSupervision as Facts
import ConnectionManagement.Properties.HandlerSupervision as HandlerFacts
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import Data.List.Relation.Unary.All as All
open import Data.Product using (_×_)
initial-bounds : SupplyBounds (M.world F.start)
initial-bounds = All.[] , All.[]
abstract
  actual-projections : Facts.Paths p₀ p28
  actual-projections = Facts.exec-projects initialized-outbound-handler-close
actual-source-execution : Facts.OTrace (X.source p₀) (X.source p28)
actual-source-execution = Facts.machine actual-projections
actual-coordinator-execution : Facts.CTrace (X.shutdown p₀) (X.shutdown p28)
actual-coordinator-execution = Facts.coordinator actual-projections
abstract
  actual-close-certificate : (Close.remaining (X.shutdown p28) ≡ []) × HandlerFacts.PhysicalWait (X.shutdown p28)
  actual-close-certificate = Facts.closed-from-initial actual-initializer initialized-outbound-handler-close refl
forked-caller-captures-valid : Capture.Captures (X.source p10)
forked-caller-captures-valid = Facts.from-initial-captures actual-initializer initialized-fork
closed-caller-captures-valid : Capture.Captures (X.source p28)
closed-caller-captures-valid = Facts.from-initial-captures actual-initializer initialized-outbound-handler-close
closed-runtime-supply-valid : Supply.Valid (X.source p28)
closed-runtime-supply-valid = Facts.from-initial-supply actual-initializer initial-bounds initialized-outbound-handler-close
