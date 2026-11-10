{-# OPTIONS --guardedness #-}

-- SI4: the inbound-governor thread fails first (InboundGovernor.hs 194-235,
-- Server.hs 165-175 at network 2f1c154). Its own catch runs while the Server
-- is still serving: deactivate, drain, final trace, rethrow. waitEither then
-- returns the failed IG thread, the race closes the accept loop, the action
-- thread is cancelled and joined, and the Server's later IG cancellation finds
-- a finished thread whose result the join reads at once.
module ConnectionManagement.Negative.ServerIGFirst where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Machine as Machine
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.ServerIGExit as Proof
import ConnectionManagement.Properties.ServerIGExitInvariants as Invariants
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.ServerIGExitProtocolFixtures as Y
import ConnectionManagement.Negative.ServerIGExitProtocolPrefix as Prefix
import ConnectionManagement.Negative.ServerIGExitCasesFixtures as Z
import ConnectionManagement.Negative.ServerIGExitRelease as Birth
open import ConnectionManagement.Negative.ServerIGExitCases using (lateBefore; latePrefix)
import ConnectionManagement.Scenarios.Admission as A
private
  module E = Exit I.bearerClosed
  module S = Server I.bearerClosed
  module N = Publication I.bearerClosed
  module P = N.P
  module Facts = Proof I.bearerClosed
  module Inv = Invariants I.bearerClosed

-- A Server stage and IG phase over a rendered model.
at : S.Stage → Bool → S.IGPhase → Y.Model → E.Exit → E.State
at st lo ph m e = E.igExitState (record (E.base (Y.render m)) { stage = st; listenerOpen = lo; ig = ph }) e

fault : S.Fault
fault = S.sync X.err
caughtExit snapshotExit invokedExit returnedExit doneExit publishedExit : E.Exit
caughtExit = E.failedExit Z.body fault
snapshotExit = record caughtExit { phase = E.traversing; snapshot = Z.rows Y.a3; remaining = Z.rows Y.a3 }
invokedExit = record snapshotExit { phase = E.invoked }
returnedExit = record snapshotExit { remaining = []; returned = Z.rows Y.a3 }
doneExit = record returnedExit { phase = E.bodyDone }
publishedExit = record doneExit { result = just fault }

-- The IG catch at the serving Server.
live caught inactive flushed snapshot invoked returned done published : E.State
live = Y.render Y.a3
caught = at S.serving true S.igCaught (Z.clear Y.a3) caughtExit
inactive = at S.serving true S.igInactive (Z.inactiveModel Y.a3) caughtExit
flushed = at S.serving true S.igFlushed (Z.flushedModel Y.a3) caughtExit
snapshot = at S.serving true S.igFlushed (Z.flushedModel Y.a3) snapshotExit
invoked = at S.serving true S.igFlushed (Z.flushedModel Y.a3) invokedExit
returned = at S.serving true S.igFlushed (Z.flushedModel Y.a3) returnedExit
done = at S.serving true S.igBodyExited (Z.flushedModel Y.a3) doneExit
published = at S.serving true S.igResultAvailable (Z.flushedModel Y.a3) publishedExit
-- The Server's race after the IG thread has finished.
after : S.Stage → Bool → E.State
after st lo = at st lo S.igResultAvailable (Z.flushedModel Y.a3) publishedExit

first1 : E.step (E.fail E.loopBoundary fault) live ≡ just caught
first1 = refl
first2 : E.step (E.run (S.scope S.deactivateIG)) caught ≡ just inactive
first2 = refl
first3 : E.step (E.run (S.scope S.flushIG)) inactive ≡ just flushed
first3 = refl
first4 : E.step E.captureSnapshot flushed ≡ just snapshot
first4 = refl
first5 : E.step E.invokeFinal snapshot ≡ just invoked
first5 = refl
first6 : E.step E.returnFinal invoked ≡ just returned
first6 = refl
first7 : E.step E.finishFinal returned ≡ just done
first7 = refl
first8 : E.step (E.run (S.scope S.publishIGResult)) done ≡ just published
first8 = refl
first9 : E.step (E.run (S.scope S.igWins)) published ≡ just (after S.closingAccept true)
first9 = refl
first10 : E.step (E.run (S.scope S.requestAcceptCancel)) (after S.closingAccept true) ≡ just (after S.acceptCancelRequested true)
first10 = refl
first11 : E.step (E.run (S.scope S.deliverAcceptAtWait)) (after S.acceptCancelRequested true) ≡ just (after S.acceptCancelDelivered true)
first11 = refl
first12 : E.step (E.run (S.scope S.closeListener)) (after S.acceptCancelDelivered true) ≡ just (after S.acceptBodyExited false)
first12 = refl
first13 : E.step (E.run (S.scope S.publishAcceptResult)) (after S.acceptBodyExited false) ≡ just (after S.acceptResultAvailable false)
first13 = refl
first14 : E.step (E.run (S.scope S.joinAccept)) (after S.acceptResultAvailable false) ≡ just (after S.acceptJoined false)
first14 = refl
first15 : E.step (E.run (S.scope S.traceStopped)) (after S.acceptJoined false) ≡ just (after S.serverStopped false)
first15 = refl
first16 : E.step (E.run (S.scope S.cancelJoinReturnedAction)) (after S.serverStopped false) ≡ just (after S.actionJoined false)
first16 = refl
first17 : E.step (E.run (S.scope S.requestIGCancel)) (after S.actionJoined false) ≡ just (after S.igCancelRequested false)
first17 = refl
first18 : E.step (E.run (S.scope S.joinIG)) (after S.igCancelRequested false) ≡ just (after S.igJoined false)
first18 = refl
first19 : E.step (E.run (S.scope S.beginCM)) (after S.igJoined false) ≡ just (after S.closingCM false)
first19 = refl

firstActions : List E.Action
firstActions =
  E.fail E.loopBoundary fault ∷ E.run (S.scope S.deactivateIG) ∷ E.run (S.scope S.flushIG) ∷
  E.captureSnapshot ∷ E.invokeFinal ∷ E.returnFinal ∷ E.finishFinal ∷ E.run (S.scope S.publishIGResult) ∷
  E.run (S.scope S.igWins) ∷ E.run (S.scope S.requestAcceptCancel) ∷ E.run (S.scope S.deliverAcceptAtWait) ∷
  E.run (S.scope S.closeListener) ∷ E.run (S.scope S.publishAcceptResult) ∷ E.run (S.scope S.joinAccept) ∷
  E.run (S.scope S.traceStopped) ∷ E.run (S.scope S.cancelJoinReturnedAction) ∷ E.run (S.scope S.requestIGCancel) ∷
  E.run (S.scope S.joinIG) ∷ E.run (S.scope S.beginCM) ∷ []
abstract
  firstPath : E.Executes live firstActions (after S.closingCM false)
  firstPath = E.next first1 (E.next first2 (E.next first3 (E.next first4 (E.next first5 (E.next first6 (E.next first7
    (E.next first8 (E.next first9 (E.next first10 (E.next first11 (E.next first12 (E.next first13 (E.next first14
    (E.next first15 (E.next first16 (E.next first17 (E.next first18 (E.next first19 E.done))))))))))))))))))
  initialized-ig-first : E.Executes X.start (lateBefore ++ firstActions) (after S.closingCM false)
  initialized-ig-first = Facts.append latePrefix firstPath
ig-first-supply : Supply.Valid (E.source (after S.closingCM false))
ig-first-supply = Inv.from-initial-supply Birth.actual-initializer (All.[] , All.[]) initialized-ig-first

-- A handler keeps running during the IG catch while the Server still serves.
handler-during-catch : E.step (Prefix.protocol (P.control A.child₀ P.commitTracer)) flushed ≡
  just (at S.serving true S.igFlushed Z.lateModel caughtExit)
handler-during-catch = refl

-- Controls: the race cannot select a live IG thread; the IG catch is entered
-- once; its loop does not resume after the catch; the join waits for the IG
-- result.
no-ig-win-while-live : E.step (E.run (S.scope S.igWins)) live ≡ nothing
no-ig-win-while-live = refl
no-second-failure : E.step (E.fail E.loopBoundary fault) caught ≡ nothing
no-second-failure = refl
no-loop-after-catch : E.step (E.run (S.run (S.runMachine (Machine.igStep IG.selectBatch)))) caught ≡ nothing
no-loop-after-catch = refl
no-join-before-result : E.step (E.run (S.scope S.joinIG)) (at S.igCancelRequested false S.igCaught (Z.clear Y.a3) caughtExit) ≡ nothing
no-join-before-result = refl
