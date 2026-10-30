{-# OPTIONS --guardedness #-}

-- Initialized release interrupted after its committed write and before a
-- blocked counter read; final callbacks preserve the nonempty published IG.
module ConnectionManagement.Negative.ServerIGExitRelease where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Properties.ServerIGExit as Proof
import ConnectionManagement.Properties.ServerIGExitInvariants as Invariants
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using (admit; consume; handler; mux)
private
  module E = Exit I.bearerClosed
  module S = Server I.bearerClosed
  module Facts = Proof I.bearerClosed
  module Inv = Invariants I.bearerClosed
  module F = X.F
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.HandlerSupervision as H
private
  module N = Publication I.bearerClosed
  module U = N.U

actual-initializer : E.initial (O.initial (Machine.initial Shared.responderMode F.empty)) ≡ just X.start
actual-initializer = refl
base : S.State → E.State
base = X.wrap
ig : IG.IGAction → E.Action
ig a = E.run (S.run (S.runMachine (Machine.igStep a)))
release : Release.Action → E.Action
release a = E.run (S.run (S.runMachine (Machine.releaseStep a)))

birth1 : E.step (E.run (S.acceptedFork A.w₀ F.r₀)) (X.start) ≡ just (base F.one)
birth1 = refl
birth2 : E.step (E.run (S.acceptedFork A.w₁ F.r₁)) (base F.one) ≡ just (base F.two)
birth2 = refl
birth3 : E.step (E.run (admit A.w₀ Admission.take)) (base F.two) ≡ just (base F.p1)
birth3 = refl
birth4 : E.step (E.run (admit A.w₀ Admission.countLimit)) (base F.p1) ≡ just (base F.p2)
birth4 = refl
birth5 : E.step (E.run (admit A.w₀ Admission.allocatePromise)) (base F.p2) ≡ just (base F.p3)
birth5 = refl
birth6 : E.step (E.run (admit A.w₀ Admission.chooseEntry)) (base F.p3) ≡ just (base F.p4)
birth6 = refl
birth7 : E.step (E.run (admit A.w₀ Admission.fork)) (base F.p4) ≡ just (base F.p5)
birth7 = refl
birth8 : E.step (E.run (admit A.w₀ Admission.putMapBack)) (base F.p5) ≡ just (base F.p6)
birth8 = refl
birth9 : E.step (E.run (admit A.w₀ Admission.readCounters)) (base F.p6) ≡ just (base F.p7)
birth9 = refl
birthActions : List E.Action
birthActions =
  (E.run (S.acceptedFork A.w₀ F.r₀)) ∷
  (E.run (S.acceptedFork A.w₁ F.r₁)) ∷
  (E.run (admit A.w₀ Admission.take)) ∷
  (E.run (admit A.w₀ Admission.countLimit)) ∷
  (E.run (admit A.w₀ Admission.allocatePromise)) ∷
  (E.run (admit A.w₀ Admission.chooseEntry)) ∷
  (E.run (admit A.w₀ Admission.fork)) ∷
  (E.run (admit A.w₀ Admission.putMapBack)) ∷
  (E.run (admit A.w₀ Admission.readCounters)) ∷ []
abstract
  birthPath : E.Executes (X.start) birthActions (base F.p7)
  birthPath = E.next birth1 (E.next birth2 (E.next birth3 (E.next birth4 (E.next birth5 (E.next birth6 (E.next birth7 (E.next birth8 (E.next birth9 (E.done)))))))))

handshake1 : E.step (E.run (handler (H.enterHandshake A.child₀))) (base F.p7) ≡ just (base F.s1)
handshake1 = refl
handshake2 : E.step (E.run (mux (U.negotiate A.child₀ I.ps duplex))) (base F.s1) ≡ just (base F.s2)
handshake2 = refl
handshake3 : E.step (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0)))) (base F.s2) ≡ just (base F.s3)
handshake3 = refl
handshake4 : E.step (E.run (mux (U.publishSuccess A.child₀))) (base F.s3) ≡ just (base F.s4)
handshake4 = refl
handshake5 : E.step (E.run (consume Handshake.readResult)) (base F.s4) ≡ just (base F.s5)
handshake5 = refl
handshake6 : E.step (E.run (consume Handshake.commitResult)) (base F.s5) ≡ just (base F.s6)
handshake6 = refl
handshake7 : E.step (E.run (consume Handshake.readResultCounters)) (base F.s6) ≡ just (base F.s7)
handshake7 = refl
handshake8 : E.step (E.run (consume Handshake.enqueueInbound)) (base F.s7) ≡ just (base F.s8)
handshake8 = refl
handshake9 : E.step (E.run (consume Handshake.returnResult)) (base F.s8) ≡ just (base F.s9)
handshake9 = refl
handshake10 : E.step (E.run (S.workerReturned A.w₀)) (base F.s9) ≡ just (base F.s10)
handshake10 = refl
handshake11 : E.step (E.run (S.workerResult A.w₀)) (base F.s10) ≡ just (X.admitted)
handshake11 = refl
handshakeActions : List E.Action
handshakeActions =
  (E.run (handler (H.enterHandshake A.child₀))) ∷
  (E.run (mux (U.negotiate A.child₀ I.ps duplex))) ∷
  (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0)))) ∷
  (E.run (mux (U.publishSuccess A.child₀))) ∷
  (E.run (consume Handshake.readResult)) ∷
  (E.run (consume Handshake.commitResult)) ∷
  (E.run (consume Handshake.readResultCounters)) ∷
  (E.run (consume Handshake.enqueueInbound)) ∷
  (E.run (consume Handshake.returnResult)) ∷
  (E.run (S.workerReturned A.w₀)) ∷
  (E.run (S.workerResult A.w₀)) ∷ []
abstract
  handshakePath : E.Executes (base F.p7) handshakeActions (X.admitted)
  handshakePath = E.next handshake1 (E.next handshake2 (E.next handshake3 (E.next handshake4 (E.next handshake5 (E.next handshake6 (E.next handshake7 (E.next handshake8 (E.next handshake9 (E.next handshake10 (E.next handshake11 (E.done)))))))))))

register1 : E.step (ig (IG.captureTime 10)) (X.admitted) ≡ just (X.g1)
register1 = refl
register2 : E.step (ig IG.registerInactivity) (X.g1) ≡ just (X.g2)
register2 = refl
register3 : E.step (ig IG.selectBatch) (X.g2) ≡ just (X.g3)
register3 = refl
register4 : E.step (ig IG.readEvent) (X.g3) ≡ just (X.g4)
register4 = refl
register5 : E.step (ig IG.registerIdleTimer) (X.g4) ≡ just (X.g5)
register5 = refl
register6 : E.step (ig IG.runResponders) (X.g5) ≡ just (X.g6)
register6 = refl
register7 : E.step (ig IG.finishBatch) (X.g6) ≡ just (X.g7)
register7 = refl
registerActions : List E.Action
registerActions =
  (ig (IG.captureTime 10)) ∷
  (ig IG.registerInactivity) ∷
  (ig IG.selectBatch) ∷
  (ig IG.readEvent) ∷
  (ig IG.registerIdleTimer) ∷
  (ig IG.runResponders) ∷
  (ig IG.finishBatch) ∷ []
abstract
  registerPath : E.Executes (X.admitted) registerActions (X.g7)
  registerPath = E.next register1 (E.next register2 (E.next register3 (E.next register4 (E.next register5 (E.next register6 (E.next register7 (E.done)))))))

call1 : E.step (ig (IG.captureTime 11)) (X.g7) ≡ just (X.r1)
call1 = refl
call2 : E.step (ig IG.registerInactivity) (X.r1) ≡ just (X.r2)
call2 = refl
call3 : E.step (ig (IG.expireTimer (ident 1))) (X.r2) ≡ just (X.r3)
call3 = refl
call4 : E.step (ig IG.selectBatch) (X.r3) ≡ just (X.r4)
call4 = refl
call5 : E.step (ig IG.readEvent) (X.r4) ≡ just (X.r5)
call5 = refl
call6 : E.step (release Release.enter) (X.r5) ≡ just (X.r6)
call6 = refl
call7 : E.step (release Release.transact) (X.r6) ≡ just (X.r7)
call7 = refl
call8 : E.step (E.run (admit A.w₁ Admission.take)) (X.r7) ≡ just (X.held)
call8 = refl
callActions : List E.Action
callActions =
  (ig (IG.captureTime 11)) ∷
  (ig IG.registerInactivity) ∷
  (ig (IG.expireTimer (ident 1))) ∷
  (ig IG.selectBatch) ∷
  (ig IG.readEvent) ∷
  (release Release.enter) ∷
  (release Release.transact) ∷
  (E.run (admit A.w₁ Admission.take)) ∷ []
abstract
  callPath : E.Executes (X.g7) callActions (X.held)
  callPath = E.next call1 (E.next call2 (E.next call3 (E.next call4 (E.next call5 (E.next call6 (E.next call7 (E.next call8 (E.done))))))))

scope1 : E.step (E.run (S.scope S.returnAction)) (X.held) ≡ just (X.atScope S.actionBodyExited true X.held)
scope1 = refl
scope2 : E.step (E.run (S.scope S.publishActionResult)) (X.atScope S.actionBodyExited true X.held) ≡ just (X.atScope S.actionResultAvailable true X.held)
scope2 = refl
scope3 : E.step (E.run (S.scope S.selectActionWinner)) (X.atScope S.actionResultAvailable true X.held) ≡ just (X.atScope S.closingAccept true X.held)
scope3 = refl
scope4 : E.step (E.run (S.scope S.requestAcceptCancel)) (X.atScope S.closingAccept true X.held) ≡ just (X.atScope S.acceptCancelRequested true X.held)
scope4 = refl
scope5 : E.step (E.run (S.scope S.deliverAcceptAtWait)) (X.atScope S.acceptCancelRequested true X.held) ≡ just (X.atScope S.acceptCancelDelivered true X.held)
scope5 = refl
scope6 : E.step (E.run (S.scope S.closeListener)) (X.atScope S.acceptCancelDelivered true X.held) ≡ just (X.atScope S.acceptBodyExited false X.held)
scope6 = refl
scope7 : E.step (E.run (S.scope S.publishAcceptResult)) (X.atScope S.acceptBodyExited false X.held) ≡ just (X.atScope S.acceptResultAvailable false X.held)
scope7 = refl
scope8 : E.step (E.run (S.scope S.joinAccept)) (X.atScope S.acceptResultAvailable false X.held) ≡ just (X.atScope S.acceptJoined false X.held)
scope8 = refl
scope9 : E.step (E.run (S.scope S.traceStopped)) (X.atScope S.acceptJoined false X.held) ≡ just (X.atScope S.serverStopped false X.held)
scope9 = refl
scope10 : E.step (E.run (S.scope S.cancelJoinReturnedAction)) (X.atScope S.serverStopped false X.held) ≡ just (X.atScope S.actionJoined false X.held)
scope10 = refl
scope11 : E.step (E.run (S.scope S.requestIGCancel)) (X.atScope S.actionJoined false X.held) ≡ just (X.atScope S.igCancelRequested false X.held)
scope11 = refl
scopeActions : List E.Action
scopeActions =
  (E.run (S.scope S.returnAction)) ∷
  (E.run (S.scope S.publishActionResult)) ∷
  (E.run (S.scope S.selectActionWinner)) ∷
  (E.run (S.scope S.requestAcceptCancel)) ∷
  (E.run (S.scope S.deliverAcceptAtWait)) ∷
  (E.run (S.scope S.closeListener)) ∷
  (E.run (S.scope S.publishAcceptResult)) ∷
  (E.run (S.scope S.joinAccept)) ∷
  (E.run (S.scope S.traceStopped)) ∷
  (E.run (S.scope S.cancelJoinReturnedAction)) ∷
  (E.run (S.scope S.requestIGCancel)) ∷ []
abstract
  scopePath : E.Executes (X.held) scopeActions (X.atScope S.igCancelRequested false X.held)
  scopePath = E.next scope1 (E.next scope2 (E.next scope3 (E.next scope4 (E.next scope5 (E.next scope6 (E.next scope7 (E.next scope8 (E.next scope9 (E.next scope10 (E.next scope11 (E.done)))))))))))

exit1 : E.step (E.receive E.releaseCounters X.err) (X.atScope S.igCancelRequested false X.held) ≡ just (X.caughtRelease)
exit1 = refl
exit2 : E.step (E.run (S.scope S.deactivateIG)) (X.caughtRelease) ≡ just (X.inactive)
exit2 = refl
exit3 : E.step (E.run (S.scope S.flushIG)) (X.inactive) ≡ just (X.flushed)
exit3 = refl
exit4 : E.step (E.captureSnapshot) (X.flushed) ≡ just (X.snapshot)
exit4 = refl
exit5 : E.step (E.invokeFinal) (X.snapshot) ≡ just (X.invoked)
exit5 = refl
exit6 : E.step (E.returnFinal) (X.invoked) ≡ just (X.returned)
exit6 = refl
exit7 : E.step (E.finishFinal) (X.returned) ≡ just (X.bodyDone)
exit7 = refl
exit8 : E.step (E.run (S.scope S.publishIGResult)) (X.bodyDone) ≡ just (X.published)
exit8 = refl
exit9 : E.step (E.run (S.scope S.joinIG)) (X.published) ≡ just (X.joined)
exit9 = refl
exitActions : List E.Action
exitActions =
  (E.receive E.releaseCounters X.err) ∷
  (E.run (S.scope S.deactivateIG)) ∷
  (E.run (S.scope S.flushIG)) ∷
  (E.captureSnapshot) ∷
  (E.invokeFinal) ∷
  (E.returnFinal) ∷
  (E.finishFinal) ∷
  (E.run (S.scope S.publishIGResult)) ∷
  (E.run (S.scope S.joinIG)) ∷ []
abstract
  exitPath : E.Executes (X.atScope S.igCancelRequested false X.held) exitActions (X.joined)
  exitPath = E.next exit1 (E.next exit2 (E.next exit3 (E.next exit4 (E.next exit5 (E.next exit6 (E.next exit7 (E.next exit8 (E.next exit9 (E.done)))))))))

actions : List E.Action
actions = birthActions ++ (handshakeActions ++ (registerActions ++ (callActions ++ (scopeActions ++ exitActions))))
abstract
  initialized : E.Executes X.start actions X.joined
  initialized = Facts.append birthPath (Facts.append handshakePath (Facts.append registerPath
    (Facts.append callPath (Facts.append scopePath exitPath))))
supply : Supply.Valid (E.source X.joined)
supply = Inv.from-initial-supply actual-initializer (All.[] , All.[]) initialized

-- These observations use the real dispatcher, not only the adapter's refusal.
actual-counter-read-retries : Machine.advance (Machine.releaseStep Release.readCounters)
  (O.core (E.source (X.atScope S.igCancelRequested false X.held))) ≡ nothing
actual-counter-read-retries = refl
committed-entry-retained : lookup (ident 0) (Shared.entries (Shared.cm (Machine.world (O.core (E.source X.joined))))) ≡
  just (Shared.terminating A.key₀ A.child₀ nothing)
committed-entry-retained = refl
other-map-lease-retained : Shared.mapCell (Shared.cm (Machine.world (O.core (E.source X.joined)))) ≡ Shared.taken A.w₁
other-map-lease-retained = refl
exact-frame-archived : E.received (E.exit X.joined) ≡ just X.receivedRelease
exact-frame-archived = refl
no-active-call : Machine.inboundRelease (O.core (E.source X.joined)) ≡ nothing
no-active-call = refl
published-registry-retained : IG.publishedState (E.governor X.joined) ≡ X.registeredState
published-registry-retained = refl
final-callbacks-returned : E.returned (E.exit X.joined) ≡ X.rows
final-callbacks-returned = refl
original-exception-published : E.result (E.exit X.joined) ≡ just (S.async X.err)
original-exception-published = refl
no-raw-cm-return : Machine.advance (Machine.releaseStep Release.returnToIG) (O.core (E.source X.joined)) ≡ nothing
no-raw-cm-return = refl
no-nonblocking-masked-receipt : E.step (E.receive E.releaseCounters X.err)
  (X.atScope S.igCancelRequested false X.r7) ≡ nothing
no-nonblocking-masked-receipt = refl
no-unflushed-snapshot : E.step E.captureSnapshot X.inactive ≡ nothing
no-unflushed-snapshot = refl
no-uninvoked-return : E.step E.returnFinal X.snapshot ≡ nothing
no-uninvoked-return = refl
no-body-exit-while-callback-pending : E.step E.finishFinal X.invoked ≡ nothing
no-body-exit-while-callback-pending = refl
no-premature-result : E.step (E.run (S.scope S.publishIGResult)) X.invoked ≡ nothing
no-premature-result = refl
no-premature-join : E.step (E.run (S.scope S.joinIG)) X.invoked ≡ nothing
no-premature-join = refl
old-profile-still-refuses-nonempty : S.step (S.scope S.finishIGBody) (E.base X.flushed) ≡ nothing
old-profile-still-refuses-nonempty = refl
no-old-body-exit-bypass : E.step (E.run (S.scope S.finishIGBody)) X.flushed ≡ nothing
no-old-body-exit-bypass = refl
no-repeat-receipt : E.step (E.receive E.releaseCounters X.err) X.caughtRelease ≡ nothing
no-repeat-receipt = refl
