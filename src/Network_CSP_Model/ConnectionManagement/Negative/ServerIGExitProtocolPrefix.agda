{-# OPTIONS --guardedness #-}

-- Initialized physical startup, actual mux notifications, masked promotion and
-- unmasked demotion. No notification or active call is injected into this path.
module ConnectionManagement.Negative.ServerIGExitProtocolPrefix where

open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux; remote)
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.ServerIGExit as Proof
import ConnectionManagement.Properties.ServerIGExitInvariants as Invariants
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Properties.HandlerResourceFacts as Resources
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.ServerIGExitProtocolFixtures as Y
import ConnectionManagement.Negative.ServerIGExitRelease as Birth
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Scenarios.Admission as A
open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using (mux)
private
  module E = Exit I.bearerClosed
  module S = Server I.bearerClosed
  module N = Publication I.bearerClosed
  module C = N.C
  module D = N.D
  module M = N.M
  module P = N.P
  module U = N.U
  module T = N.S
  module Facts = Proof I.bearerClosed
  module Inv = Invariants I.bearerClosed

same-registered-checkpoint : Y.render Y.root ≡ X.g7
same-registered-checkpoint = refl
beforeActions : List E.Action
beforeActions = Birth.birthActions ++ (Birth.handshakeActions ++ Birth.registerActions)
abstract
  beforePath : E.Executes X.start beforeActions (Y.render Y.root)
  beforePath = Facts.append Birth.birthPath (Facts.append Birth.handshakePath Birth.registerPath)
protocol : P.Action → E.Action
protocol a = E.run (S.run (N.run (C.run (D.run (D.wrapMonitor (M.run a))))))
monitor : M.Action → E.Action
monitor a = E.run (S.run (N.run (C.run (D.run (D.wrapMonitor a)))))
delta : D.Action → E.Action
delta a = E.run (S.run (N.run (C.run a)))
ig : IG.IGAction → E.Action
ig = Birth.ig
remote : Remote.Action → E.Action
remote a = E.run (S.run (S.runMachine (Machine.remoteStep a)))

startup1 : E.step (E.run (mux (U.startupStep A.child₀ T.allocateBuffer))) (Y.render Y.root) ≡ just (Y.render Y.s1)
startup1 = refl
startup2 : E.step (E.run (mux (U.startupStep A.child₀ T.createBearer))) (Y.render Y.s1) ≡ just (Y.render Y.s2)
startup2 = refl
startup3 : E.step (E.run (mux (U.startupStep A.child₀ T.enterRun))) (Y.render Y.s2) ≡ just (Y.render Y.s3)
startup3 = refl
startup4 : E.step (E.run (mux (U.startupStep A.child₀ T.traceStarting))) (Y.render Y.s3) ≡ just (Y.render Y.s4)
startup4 = refl
startup5 : E.step (E.run (mux (U.startupStep A.child₀ T.allocateEgress))) (Y.render Y.s4) ≡ just (Y.render Y.s5)
startup5 = refl
startup6 : E.step (E.run (mux (U.startupStep A.child₀ T.openPool))) (Y.render Y.s5) ≡ just (Y.render Y.s6)
startup6 = refl
startup7 : E.step (E.run (mux (U.startupStep A.child₀ (T.forkMuxer (ident 0))))) (Y.render Y.s6) ≡ just (Y.render Y.s7)
startup7 = refl
startup8 : E.step (E.run (mux (U.startupStep A.child₀ T.registerMuxer))) (Y.render Y.s7) ≡ just (Y.render Y.s8)
startup8 = refl
startup9 : E.step (E.run (mux (U.startupStep A.child₀ (T.forkDemuxer (ident 1))))) (Y.render Y.s8) ≡ just (Y.render Y.s9)
startup9 = refl
startup10 : E.step (E.run (mux (U.startupStep A.child₀ T.registerDemuxer))) (Y.render Y.s9) ≡ just (Y.render Y.s10)
startup10 = refl
startup11 : E.step (E.run (mux (U.startupStep A.child₀ T.traceMature))) (Y.render Y.s10) ≡ just (Y.render Y.s11)
startup11 = refl
startup12 : E.step (E.run (mux (U.startupStep A.child₀ T.enterMonitor))) (Y.render Y.s11) ≡ just (Y.render Y.s12)
startup12 = refl
startupActions : List E.Action
startupActions =
  (E.run (mux (U.startupStep A.child₀ T.allocateBuffer))) ∷
  (E.run (mux (U.startupStep A.child₀ T.createBearer))) ∷
  (E.run (mux (U.startupStep A.child₀ T.enterRun))) ∷
  (E.run (mux (U.startupStep A.child₀ T.traceStarting))) ∷
  (E.run (mux (U.startupStep A.child₀ T.allocateEgress))) ∷
  (E.run (mux (U.startupStep A.child₀ T.openPool))) ∷
  (E.run (mux (U.startupStep A.child₀ (T.forkMuxer (ident 0))))) ∷
  (E.run (mux (U.startupStep A.child₀ T.registerMuxer))) ∷
  (E.run (mux (U.startupStep A.child₀ (T.forkDemuxer (ident 1))))) ∷
  (E.run (mux (U.startupStep A.child₀ T.registerDemuxer))) ∷
  (E.run (mux (U.startupStep A.child₀ T.traceMature))) ∷
  (E.run (mux (U.startupStep A.child₀ T.enterMonitor))) ∷ []
abstract
  startupPath : E.Executes (Y.render Y.root) startupActions (Y.render Y.s12)
  startupPath = E.next startup1 (E.next startup2 (E.next startup3 (E.next startup4 (E.next startup5 (E.next startup6 (E.next startup7 (E.next startup8 (E.next startup9 (E.next startup10 (E.next startup11 (E.next startup12 (E.done))))))))))))

notification1 : E.step (protocol (P.control A.child₀ P.selectCommand)) (Y.render Y.s12) ≡ just (Y.render Y.a1)
notification1 = refl
notification2 : E.step (protocol (P.control A.child₀ (P.demand 1))) (Y.render Y.a1) ≡ just (Y.render Y.a2)
notification2 = refl
notification3 : E.step (protocol (P.control A.child₀ P.sampleTracer)) (Y.render Y.a2) ≡ just (Y.render Y.a3)
notification3 = refl
notification4 : E.step (protocol (P.control A.child₀ P.commitTracer)) (Y.render Y.a3) ≡ just (Y.render Y.a4)
notification4 = refl
notificationActions : List E.Action
notificationActions =
  (protocol (P.control A.child₀ P.selectCommand)) ∷
  (protocol (P.control A.child₀ (P.demand 1))) ∷
  (protocol (P.control A.child₀ P.sampleTracer)) ∷
  (protocol (P.control A.child₀ P.commitTracer)) ∷ []
abstract
  notificationPath : E.Executes (Y.render Y.s12) notificationActions (Y.render Y.a4)
  notificationPath = E.next notification1 (E.next notification2 (E.next notification3 (E.next notification4 (E.done))))

enterPromotion1 : E.step (ig (IG.captureTime 11)) (Y.render Y.a4) ≡ just (Y.render Y.g1)
enterPromotion1 = refl
enterPromotion2 : E.step (ig IG.registerInactivity) (Y.render Y.g1) ≡ just (Y.render Y.g2)
enterPromotion2 = refl
enterPromotion3 : E.step (ig IG.selectBatch) (Y.render Y.g2) ≡ just (Y.render Y.g3)
enterPromotion3 = refl
enterPromotion4 : E.step (ig IG.readEvent) (Y.render Y.g3) ≡ just (Y.render Y.g4)
enterPromotion4 = refl
enterPromotion5 : E.step (remote Remote.enter) (Y.render Y.g4) ≡ just (Y.render Y.g5)
enterPromotion5 = refl
enterPromotionActions : List E.Action
enterPromotionActions =
  (ig (IG.captureTime 11)) ∷
  (ig IG.registerInactivity) ∷
  (ig IG.selectBatch) ∷
  (ig IG.readEvent) ∷
  (remote Remote.enter) ∷ []
abstract
  enterPromotionPath : E.Executes (Y.render Y.a4) enterPromotionActions (Y.render Y.g5)
  enterPromotionPath = E.next enterPromotion1 (E.next enterPromotion2 (E.next enterPromotion3 (E.next enterPromotion4 (E.next enterPromotion5 (E.done)))))

promotion1 : E.step (remote Remote.transact) (Y.render Y.g5) ≡ just (Y.render Y.g6)
promotion1 = refl
promotion2 : E.step (remote Remote.checkAssertion) (Y.render Y.g6) ≡ just (Y.render Y.g7)
promotion2 = refl
promotion3 : E.step (remote Remote.readCounters) (Y.render Y.g7) ≡ just (Y.render Y.g8)
promotion3 = refl
promotion4 : E.step (remote Remote.returnToIG) (Y.render Y.g8) ≡ just (Y.render Y.g9)
promotion4 = refl
promotion5 : E.step (ig IG.commitDecision) (Y.render Y.g9) ≡ just (Y.render Y.g10)
promotion5 = refl
promotion6 : E.step (ig IG.readEvent) (Y.render Y.g10) ≡ just (Y.render Y.g11)
promotion6 = refl
promotion7 : E.step (ig IG.commitDecision) (Y.render Y.g11) ≡ just (Y.render Y.g12)
promotion7 = refl
promotion8 : E.step (ig IG.finishBatch) (Y.render Y.g12) ≡ just (Y.render Y.g13)
promotion8 = refl
promotionActions : List E.Action
promotionActions =
  (remote Remote.transact) ∷
  (remote Remote.checkAssertion) ∷
  (remote Remote.readCounters) ∷
  (remote Remote.returnToIG) ∷
  (ig IG.commitDecision) ∷
  (ig IG.readEvent) ∷
  (ig IG.commitDecision) ∷
  (ig IG.finishBatch) ∷ []
abstract
  promotionPath : E.Executes (Y.render Y.g5) promotionActions (Y.render Y.g13)
  promotionPath = E.next promotion1 (E.next promotion2 (E.next promotion3 (E.next promotion4 (E.next promotion5 (E.next promotion6 (E.next promotion7 (E.next promotion8 (E.done))))))))

completion1 : E.step (protocol (P.control A.child₀ P.finishStart)) (Y.render Y.g13) ≡ just (Y.render Y.j1)
completion1 = refl
completion2 : E.step (protocol (P.forkResponder A.child₀ (ident 10) (ident 0))) (Y.render Y.j1) ≡ just (Y.render Y.j2)
completion2 = refl
completion3 : E.step (protocol (P.registerProtocol (ident 10))) (Y.render Y.j2) ≡ just (Y.render Y.j3)
completion3 = refl
completion4 : E.step (protocol (P.protocolReturned (ident 10))) (Y.render Y.j3) ≡ just (Y.render Y.j4)
completion4 = refl
completion5 : E.step (protocol (P.commitClean (ident 10))) (Y.render Y.j4) ≡ just (Y.render Y.j5)
completion5 = refl
completion6 : E.step (protocol (P.returnProtocol (ident 10))) (Y.render Y.j5) ≡ just (Y.render Y.j6)
completion6 = refl
completion7 : E.step (protocol (P.publishProtocol (ident 10))) (Y.render Y.j6) ≡ just (Y.render Y.j7)
completion7 = refl
completion8 : E.step (monitor (M.consume A.child₀)) (Y.render Y.j7) ≡ just (Y.render Y.j8)
completion8 = refl
completion9 : E.step (monitor (M.handleSelected A.child₀)) (Y.render Y.j8) ≡ just (Y.render Y.j9)
completion9 = refl
completion10 : E.step (monitor (M.sampleTracer A.child₀)) (Y.render Y.j9) ≡ just (Y.render Y.j10)
completion10 = refl
completion11 : E.step (monitor (M.commitTracer A.child₀)) (Y.render Y.j10) ≡ just (Y.render Y.j11)
completion11 = refl
completion12 : E.step (delta (D.beginDeltaQ A.child₀)) (Y.render Y.j11) ≡ just (Y.render Y.j12)
completion12 = refl
completion13 : E.step (delta (D.observeReturn A.child₀)) (Y.render Y.j12) ≡ just (Y.render Y.j13)
completion13 = refl
completionActions : List E.Action
completionActions =
  (protocol (P.control A.child₀ P.finishStart)) ∷
  (protocol (P.forkResponder A.child₀ (ident 10) (ident 0))) ∷
  (protocol (P.registerProtocol (ident 10))) ∷
  (protocol (P.protocolReturned (ident 10))) ∷
  (protocol (P.commitClean (ident 10))) ∷
  (protocol (P.returnProtocol (ident 10))) ∷
  (protocol (P.publishProtocol (ident 10))) ∷
  (monitor (M.consume A.child₀)) ∷
  (monitor (M.handleSelected A.child₀)) ∷
  (monitor (M.sampleTracer A.child₀)) ∷
  (monitor (M.commitTracer A.child₀)) ∷
  (delta (D.beginDeltaQ A.child₀)) ∷
  (delta (D.observeReturn A.child₀)) ∷ []
abstract
  completionPath : E.Executes (Y.render Y.g13) completionActions (Y.render Y.j13)
  completionPath = E.next completion1 (E.next completion2 (E.next completion3 (E.next completion4 (E.next completion5 (E.next completion6 (E.next completion7 (E.next completion8 (E.next completion9 (E.next completion10 (E.next completion11 (E.next completion12 (E.next completion13 (E.done)))))))))))))

demotion1 : E.step (ig (IG.captureTime 12)) (Y.render Y.j13) ≡ just (Y.render Y.d1)
demotion1 = refl
demotion2 : E.step (ig IG.registerInactivity) (Y.render Y.d1) ≡ just (Y.render Y.d2)
demotion2 = refl
demotion3 : E.step (ig IG.selectBatch) (Y.render Y.d2) ≡ just (Y.render Y.d3)
demotion3 = refl
demotion4 : E.step (ig IG.readEvent) (Y.render Y.d3) ≡ just (Y.render Y.d4)
demotion4 = refl
demotion5 : E.step (ig IG.restart) (Y.render Y.d4) ≡ just (Y.render Y.d5)
demotion5 = refl
demotion6 : E.step (ig IG.readEvent) (Y.render Y.d5) ≡ just (Y.render Y.d6)
demotion6 = refl
demotion7 : E.step (ig IG.commitDecision) (Y.render Y.d6) ≡ just (Y.render Y.d7)
demotion7 = refl
demotion8 : E.step (ig IG.readEvent) (Y.render Y.d7) ≡ just (Y.render Y.d8)
demotion8 = refl
demotion9 : E.step (remote Remote.enter) (Y.render Y.d8) ≡ just (Y.render Y.d9)
demotion9 = refl
demotion10 : E.step (remote Remote.transact) (Y.render Y.d9) ≡ just (Y.render Y.d10)
demotion10 = refl
demotionActions : List E.Action
demotionActions =
  (ig (IG.captureTime 12)) ∷
  (ig IG.registerInactivity) ∷
  (ig IG.selectBatch) ∷
  (ig IG.readEvent) ∷
  (ig IG.restart) ∷
  (ig IG.readEvent) ∷
  (ig IG.commitDecision) ∷
  (ig IG.readEvent) ∷
  (remote Remote.enter) ∷
  (remote Remote.transact) ∷ []
abstract
  demotionPath : E.Executes (Y.render Y.j13) demotionActions (Y.render Y.d10)
  demotionPath = E.next demotion1 (E.next demotion2 (E.next demotion3 (E.next demotion4 (E.next demotion5 (E.next demotion6 (E.next demotion7 (E.next demotion8 (E.next demotion9 (E.next demotion10 (E.done))))))))))

toPromotionActions : List E.Action
toPromotionActions = beforeActions ++ (startupActions ++ (notificationActions ++ enterPromotionActions))
abstract
  initialized-promotion : E.Executes X.start toPromotionActions (Y.render Y.g5)
  initialized-promotion = Facts.append beforePath (Facts.append startupPath (Facts.append notificationPath enterPromotionPath))
  toPromotionWrite : E.Executes X.start (toPromotionActions ++ (remote Remote.transact ∷ remote Remote.checkAssertion ∷ [])) (Y.render Y.g7)
  toPromotionWrite = Facts.append initialized-promotion (E.next promotion1 (E.next promotion2 E.done))
allActions : List E.Action
allActions = toPromotionActions ++ (promotionActions ++ (completionActions ++ demotionActions))
abstract
  initialized-demotion : E.Executes X.start allActions (Y.render Y.d10)
  initialized-demotion = Facts.append initialized-promotion (Facts.append promotionPath (Facts.append completionPath demotionPath))
supply : Supply.Valid (E.source (Y.render Y.d10))
supply = Inv.from-initial-supply Birth.actual-initializer (All.[] , All.[]) initialized-demotion

-- The fixed original handler resources survive the entire physical/CM prefix.
resourceActions : List E.Action
resourceActions = startupActions ++ (notificationActions ++ (enterPromotionActions ++
  (promotionActions ++ (completionActions ++ demotionActions))))
resourcePath : E.Executes (Y.render Y.root) resourceActions (Y.render Y.d10)
resourcePath = Facts.append startupPath (Facts.append notificationPath (Facts.append enterPromotionPath
  (Facts.append promotionPath (Facts.append completionPath demotionPath))))
resources : Resources.Facts A.child₀ I.captured (Machine.world (O.core (E.source (Y.render Y.d10))))
resources = Inv.For.exec-preserves A.child₀ I.captured resourcePath (refl , (Y.idle , refl) , (Shared.handling A.child₀ , refl))
