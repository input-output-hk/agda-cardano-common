{-# OPTIONS --guardedness #-}

-- Initialized release receipts before its first STM commit and while its
-- captured throwTo is observed blocked, without manufacturing target receipt.
module ConnectionManagement.Negative.ServerIGExitSend where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux; entry)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.ServerIGExit as Proof
import ConnectionManagement.Properties.ServerIGExitScope as Scope
import ConnectionManagement.Properties.ServerIGExitInvariants as Invariants
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.ServerIGExitProtocolFixtures as Y
import ConnectionManagement.Negative.ServerIGExitCasesFixtures as Z
import ConnectionManagement.Negative.ServerIGExitRelease as R
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Scenarios.Admission as A
open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using (admit)
private
  module E = Exit I.bearerClosed
  module S = Server I.bearerClosed
  module N = Publication I.bearerClosed
  module Facts = Proof I.bearerClosed
  module K = Scope I.bearerClosed
  module Inv = Invariants I.bearerClosed

entry : Y.Model
entry = record Y.root { governor = IG.runtimeState X.registeredState 3 IG.inCM X.expiredEngine; cmRelease = just X.releaseFrame }
written counted sending : Y.Model
written = record entry { world = X.writtenWorld; cmRelease = just X.writtenFrame }
counted = record written { cmRelease = just (record X.writtenFrame { pc = Release.cancellation }) }
sendFrame : Release.Frame
sendFrame = record X.writtenFrame { pc = Release.delivering A.child₀ }
sending = record written { cmRelease = just sendFrame }
beforeCommit : Y.Model
beforeCommit = Z.lock entry
readReceipt sendReceipt : E.Receipt
readReceipt = E.receipt E.releaseRead X.err (just (E.releaseCall X.releaseFrame))
sendReceipt = E.receipt E.releaseSend X.err (just (E.releaseCall sendFrame))
same-entry : Y.render entry ≡ X.r6
same-entry = refl
same-written : Y.render written ≡ X.r7
same-written = refl

toEntry : List E.Action
toEntry = R.birthActions ++ (R.handshakeActions ++ (R.registerActions ++
  (R.ig (IG.captureTime 11) ∷ R.ig IG.registerInactivity ∷ R.ig (IG.expireTimer (ident 1)) ∷
   R.ig IG.selectBatch ∷ R.ig IG.readEvent ∷ R.release Release.enter ∷ [])))
abstract
  entryPath : E.Executes X.start toEntry (Y.render entry)
  entryPath = Facts.append R.birthPath (Facts.append R.handshakePath (Facts.append R.registerPath
    (E.next R.call1 (E.next R.call2 (E.next R.call3 (E.next R.call4 (E.next R.call5 (E.next R.call6 E.done))))))))
before-commit-take : E.step (E.run (admit A.w₁ Admission.take)) (Y.render entry) ≡ just (Y.render beforeCommit)
before-commit-take = refl
transact : E.step (R.release Release.transact) (Y.render entry) ≡ just (Y.render written)
transact = R.call7
count : E.step (R.release Release.readCounters) (Y.render written) ≡ just (Y.render counted)
count = refl
request : E.step (R.release Release.requestCancellation) (Y.render counted) ≡ just (Y.render sending)
request = refl
read1 : E.step (E.receive E.releaseRead X.err) (K.atStage S.igCancelRequested false (Y.render beforeCommit)) ≡ just (Z.caught readReceipt beforeCommit)
read1 = refl
read2 : E.step (E.run (S.scope S.deactivateIG)) (Z.caught readReceipt beforeCommit) ≡ just (Z.inactive readReceipt beforeCommit)
read2 = refl
read3 : E.step (E.run (S.scope S.flushIG)) (Z.inactive readReceipt beforeCommit) ≡ just (Z.flushed readReceipt beforeCommit)
read3 = refl
read4 : E.step (E.captureSnapshot) (Z.flushed readReceipt beforeCommit) ≡ just (Z.snapshot readReceipt beforeCommit)
read4 = refl
read5 : E.step (E.invokeFinal) (Z.snapshot readReceipt beforeCommit) ≡ just (Z.invoked readReceipt beforeCommit)
read5 = refl
read6 : E.step (E.returnFinal) (Z.invoked readReceipt beforeCommit) ≡ just (Z.returned readReceipt beforeCommit)
read6 = refl
read7 : E.step (E.finishFinal) (Z.returned readReceipt beforeCommit) ≡ just (Z.done readReceipt beforeCommit)
read7 = refl
read8 : E.step (E.run (S.scope S.publishIGResult)) (Z.done readReceipt beforeCommit) ≡ just (Z.published readReceipt beforeCommit)
read8 = refl
read9 : E.step (E.run (S.scope S.joinIG)) (Z.published readReceipt beforeCommit) ≡ just (Z.joined readReceipt beforeCommit)
read9 = refl
readActions : List E.Action
readActions =
  (E.receive E.releaseRead X.err) ∷
  (E.run (S.scope S.deactivateIG)) ∷
  (E.run (S.scope S.flushIG)) ∷
  (E.captureSnapshot) ∷
  (E.invokeFinal) ∷
  (E.returnFinal) ∷
  (E.finishFinal) ∷
  (E.run (S.scope S.publishIGResult)) ∷
  (E.run (S.scope S.joinIG)) ∷ []
abstract
  readPath : E.Executes (K.atStage S.igCancelRequested false (Y.render beforeCommit)) readActions (Z.joined readReceipt beforeCommit)
  readPath = E.next read1 (E.next read2 (E.next read3 (E.next read4 (E.next read5 (E.next read6 (E.next read7 (E.next read8 (E.next read9 (E.done)))))))))

send1 : E.step (E.receive E.releaseSend X.err) (K.atStage S.igCancelRequested false (Y.render sending)) ≡ just (Z.caught sendReceipt sending)
send1 = refl
send2 : E.step (E.run (S.scope S.deactivateIG)) (Z.caught sendReceipt sending) ≡ just (Z.inactive sendReceipt sending)
send2 = refl
send3 : E.step (E.run (S.scope S.flushIG)) (Z.inactive sendReceipt sending) ≡ just (Z.flushed sendReceipt sending)
send3 = refl
send4 : E.step (E.captureSnapshot) (Z.flushed sendReceipt sending) ≡ just (Z.snapshot sendReceipt sending)
send4 = refl
send5 : E.step (E.invokeFinal) (Z.snapshot sendReceipt sending) ≡ just (Z.invoked sendReceipt sending)
send5 = refl
send6 : E.step (E.returnFinal) (Z.invoked sendReceipt sending) ≡ just (Z.returned sendReceipt sending)
send6 = refl
send7 : E.step (E.finishFinal) (Z.returned sendReceipt sending) ≡ just (Z.done sendReceipt sending)
send7 = refl
send8 : E.step (E.run (S.scope S.publishIGResult)) (Z.done sendReceipt sending) ≡ just (Z.published sendReceipt sending)
send8 = refl
send9 : E.step (E.run (S.scope S.joinIG)) (Z.published sendReceipt sending) ≡ just (Z.joined sendReceipt sending)
send9 = refl
sendActions : List E.Action
sendActions =
  (E.receive E.releaseSend X.err) ∷
  (E.run (S.scope S.deactivateIG)) ∷
  (E.run (S.scope S.flushIG)) ∷
  (E.captureSnapshot) ∷
  (E.invokeFinal) ∷
  (E.returnFinal) ∷
  (E.finishFinal) ∷
  (E.run (S.scope S.publishIGResult)) ∷
  (E.run (S.scope S.joinIG)) ∷ []
abstract
  sendPath : E.Executes (K.atStage S.igCancelRequested false (Y.render sending)) sendActions (Z.joined sendReceipt sending)
  sendPath = E.next send1 (E.next send2 (E.next send3 (E.next send4 (E.next send5 (E.next send6 (E.next send7 (E.next send8 (E.next send9 (E.done)))))))))

readAll sendAll : List E.Action
readAll = toEntry ++ (E.run (admit A.w₁ Admission.take) ∷ (K.actions ++ readActions))
sendAll = toEntry ++ (R.release Release.transact ∷ R.release Release.readCounters ∷ R.release Release.requestCancellation ∷ (K.actions ++ sendActions))
abstract
  initialized-read : E.Executes X.start readAll (Z.joined readReceipt beforeCommit)
  initialized-read = Facts.append entryPath (E.next before-commit-take (Facts.append (K.path (Y.render beforeCommit)) readPath))
  initialized-send : E.Executes X.start sendAll (Z.joined sendReceipt sending)
  initialized-send = Facts.append entryPath (E.next transact (E.next count (E.next request
    (Facts.append (K.path (Y.render sending)) sendPath))))
read-supply : Supply.Valid (E.source (Z.joined readReceipt beforeCommit))
read-supply = Inv.from-initial-supply R.actual-initializer (All.[] , All.[]) initialized-read
send-supply : Supply.Valid (E.source (Z.joined sendReceipt sending))
send-supply = Inv.from-initial-supply R.actual-initializer (All.[] , All.[]) initialized-send
real-read-retries : Machine.advance (Machine.releaseStep Release.transact) (O.core (E.source (Y.render beforeCommit))) ≡ nothing
real-read-retries = refl
pre-commit-keeps-idle : lookup (ident 0) (Shared.entries (Shared.cm (Machine.world (O.core (E.source (Z.joined readReceipt beforeCommit)))))) ≡ just Y.idle
pre-commit-keeps-idle = refl
send-frame-archived : E.received (E.exit (Z.joined sendReceipt sending)) ≡ just sendReceipt
send-frame-archived = refl
no-target-result-invented : N.W.resultReady A.child₀ (N.R.base (N.raw (S.base (E.base (Z.joined sendReceipt sending))))) ≡ false
no-target-result-invented = refl
no-active-sender : Machine.inboundRelease (O.core (E.source (Z.joined sendReceipt sending))) ≡ nothing
no-active-sender = refl
