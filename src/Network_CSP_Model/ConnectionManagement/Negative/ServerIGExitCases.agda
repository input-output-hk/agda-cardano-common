{-# OPTIONS --guardedness #-}

-- Initialized CM exits and an actual mux enqueue after the final IG drain.
module ConnectionManagement.Negative.ServerIGExitCases where

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
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.ServerIGExit as Proof
import ConnectionManagement.Properties.ServerIGExitScope as Scope
import ConnectionManagement.Properties.ServerIGExitInvariants as Invariants
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.ServerIGExitProtocolFixtures as Y
import ConnectionManagement.Negative.ServerIGExitProtocolPrefix as Prefix
import ConnectionManagement.Negative.ServerIGExitCasesFixtures as Z
import ConnectionManagement.Negative.ServerIGExitRelease as Birth
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Scenarios.Admission as A
open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using (admit)
private
  module E = Exit I.bearerClosed
  module S = Server I.bearerClosed
  module N = Publication I.bearerClosed
  module P = N.P
  module Facts = Proof I.bearerClosed
  module K = Scope I.bearerClosed
  module Inv = Invariants I.bearerClosed

core : E.State → Machine.Configuration
core s = O.core (E.source s)
heap : E.State → Shared.EntryHeap
heap s = Shared.entries (Shared.cm (Machine.world (core s)))
pre-lock : E.step (E.run (admit A.w₁ Admission.take)) (Y.render Y.g5) ≡ just (Y.render Z.beforePromotion)
pre-lock = refl
post-lock : E.step (E.run (admit A.w₁ Admission.take)) (Y.render Y.g7) ≡ just (Y.render Z.afterPromotion)
post-lock = refl

pre1 : E.step (E.receive E.promoteRead X.err) (K.atStage S.igCancelRequested false (Y.render Z.beforePromotion)) ≡ just (Z.caught Z.pre Z.beforePromotion)
pre1 = refl
pre2 : E.step (E.run (S.scope S.deactivateIG)) (Z.caught Z.pre Z.beforePromotion) ≡ just (Z.inactive Z.pre Z.beforePromotion)
pre2 = refl
pre3 : E.step (E.run (S.scope S.flushIG)) (Z.inactive Z.pre Z.beforePromotion) ≡ just (Z.flushed Z.pre Z.beforePromotion)
pre3 = refl
pre4 : E.step (E.captureSnapshot) (Z.flushed Z.pre Z.beforePromotion) ≡ just (Z.snapshot Z.pre Z.beforePromotion)
pre4 = refl
pre5 : E.step (E.invokeFinal) (Z.snapshot Z.pre Z.beforePromotion) ≡ just (Z.invoked Z.pre Z.beforePromotion)
pre5 = refl
pre6 : E.step (E.returnFinal) (Z.invoked Z.pre Z.beforePromotion) ≡ just (Z.returned Z.pre Z.beforePromotion)
pre6 = refl
pre7 : E.step (E.finishFinal) (Z.returned Z.pre Z.beforePromotion) ≡ just (Z.done Z.pre Z.beforePromotion)
pre7 = refl
pre8 : E.step (E.run (S.scope S.publishIGResult)) (Z.done Z.pre Z.beforePromotion) ≡ just (Z.published Z.pre Z.beforePromotion)
pre8 = refl
pre9 : E.step (E.run (S.scope S.joinIG)) (Z.published Z.pre Z.beforePromotion) ≡ just (Z.joined Z.pre Z.beforePromotion)
pre9 = refl
preActions : List E.Action
preActions =
  (E.receive E.promoteRead X.err) ∷
  (E.run (S.scope S.deactivateIG)) ∷
  (E.run (S.scope S.flushIG)) ∷
  (E.captureSnapshot) ∷
  (E.invokeFinal) ∷
  (E.returnFinal) ∷
  (E.finishFinal) ∷
  (E.run (S.scope S.publishIGResult)) ∷
  (E.run (S.scope S.joinIG)) ∷ []
abstract
  prePath : E.Executes (K.atStage S.igCancelRequested false (Y.render Z.beforePromotion)) preActions (Z.joined Z.pre Z.beforePromotion)
  prePath = E.next pre1 (E.next pre2 (E.next pre3 (E.next pre4 (E.next pre5 (E.next pre6 (E.next pre7 (E.next pre8 (E.next pre9 (E.done)))))))))

post1 : E.step (E.receive E.promoteCounters X.err) (K.atStage S.igCancelRequested false (Y.render Z.afterPromotion)) ≡ just (Z.caught Z.post Z.afterPromotion)
post1 = refl
post2 : E.step (E.run (S.scope S.deactivateIG)) (Z.caught Z.post Z.afterPromotion) ≡ just (Z.inactive Z.post Z.afterPromotion)
post2 = refl
post3 : E.step (E.run (S.scope S.flushIG)) (Z.inactive Z.post Z.afterPromotion) ≡ just (Z.flushed Z.post Z.afterPromotion)
post3 = refl
post4 : E.step (E.captureSnapshot) (Z.flushed Z.post Z.afterPromotion) ≡ just (Z.snapshot Z.post Z.afterPromotion)
post4 = refl
post5 : E.step (E.invokeFinal) (Z.snapshot Z.post Z.afterPromotion) ≡ just (Z.invoked Z.post Z.afterPromotion)
post5 = refl
post6 : E.step (E.returnFinal) (Z.invoked Z.post Z.afterPromotion) ≡ just (Z.returned Z.post Z.afterPromotion)
post6 = refl
post7 : E.step (E.finishFinal) (Z.returned Z.post Z.afterPromotion) ≡ just (Z.done Z.post Z.afterPromotion)
post7 = refl
post8 : E.step (E.run (S.scope S.publishIGResult)) (Z.done Z.post Z.afterPromotion) ≡ just (Z.published Z.post Z.afterPromotion)
post8 = refl
post9 : E.step (E.run (S.scope S.joinIG)) (Z.published Z.post Z.afterPromotion) ≡ just (Z.joined Z.post Z.afterPromotion)
post9 = refl
postActions : List E.Action
postActions =
  (E.receive E.promoteCounters X.err) ∷
  (E.run (S.scope S.deactivateIG)) ∷
  (E.run (S.scope S.flushIG)) ∷
  (E.captureSnapshot) ∷
  (E.invokeFinal) ∷
  (E.returnFinal) ∷
  (E.finishFinal) ∷
  (E.run (S.scope S.publishIGResult)) ∷
  (E.run (S.scope S.joinIG)) ∷ []
abstract
  postPath : E.Executes (K.atStage S.igCancelRequested false (Y.render Z.afterPromotion)) postActions (Z.joined Z.post Z.afterPromotion)
  postPath = E.next post1 (E.next post2 (E.next post3 (E.next post4 (E.next post5 (E.next post6 (E.next post7 (E.next post8 (E.next post9 (E.done)))))))))

demote1 : E.step (E.receive E.demoteBoundary X.err) (K.atStage S.igCancelRequested false (Y.render Y.d10)) ≡ just (Z.caught Z.demote Y.d10)
demote1 = refl
demote2 : E.step (E.run (S.scope S.deactivateIG)) (Z.caught Z.demote Y.d10) ≡ just (Z.inactive Z.demote Y.d10)
demote2 = refl
demote3 : E.step (E.run (S.scope S.flushIG)) (Z.inactive Z.demote Y.d10) ≡ just (Z.flushed Z.demote Y.d10)
demote3 = refl
demote4 : E.step (E.captureSnapshot) (Z.flushed Z.demote Y.d10) ≡ just (Z.snapshot Z.demote Y.d10)
demote4 = refl
demote5 : E.step (E.invokeFinal) (Z.snapshot Z.demote Y.d10) ≡ just (Z.invoked Z.demote Y.d10)
demote5 = refl
demote6 : E.step (E.returnFinal) (Z.invoked Z.demote Y.d10) ≡ just (Z.returned Z.demote Y.d10)
demote6 = refl
demote7 : E.step (E.finishFinal) (Z.returned Z.demote Y.d10) ≡ just (Z.done Z.demote Y.d10)
demote7 = refl
demote8 : E.step (E.run (S.scope S.publishIGResult)) (Z.done Z.demote Y.d10) ≡ just (Z.published Z.demote Y.d10)
demote8 = refl
demote9 : E.step (E.run (S.scope S.joinIG)) (Z.published Z.demote Y.d10) ≡ just (Z.joined Z.demote Y.d10)
demote9 = refl
demoteActions : List E.Action
demoteActions =
  (E.receive E.demoteBoundary X.err) ∷
  (E.run (S.scope S.deactivateIG)) ∷
  (E.run (S.scope S.flushIG)) ∷
  (E.captureSnapshot) ∷
  (E.invokeFinal) ∷
  (E.returnFinal) ∷
  (E.finishFinal) ∷
  (E.run (S.scope S.publishIGResult)) ∷
  (E.run (S.scope S.joinIG)) ∷ []
abstract
  demotePath : E.Executes (K.atStage S.igCancelRequested false (Y.render Y.d10)) demoteActions (Z.joined Z.demote Y.d10)
  demotePath = E.next demote1 (E.next demote2 (E.next demote3 (E.next demote4 (E.next demote5 (E.next demote6 (E.next demote7 (E.next demote8 (E.next demote9 (E.done)))))))))

-- Every finalizer follows the checked owned-scope cancellation request.
preAll postAll demoteAll : List E.Action
preAll = Prefix.toPromotionActions ++ (E.run (admit A.w₁ Admission.take) ∷ (K.actions ++ preActions))
postAll = (Prefix.toPromotionActions ++ (Prefix.remote Remote.transact ∷ Prefix.remote Remote.checkAssertion ∷ [])) ++
  (E.run (admit A.w₁ Admission.take) ∷ (K.actions ++ postActions))
demoteAll = Prefix.allActions ++ (K.actions ++ demoteActions)
abstract
  initialized-pre : E.Executes X.start preAll (Z.joined Z.pre Z.beforePromotion)
  initialized-pre = Facts.append Prefix.initialized-promotion
    (E.next pre-lock (Facts.append (K.path (Y.render Z.beforePromotion)) prePath))
  initialized-post : E.Executes X.start postAll (Z.joined Z.post Z.afterPromotion)
  initialized-post = Facts.append Prefix.toPromotionWrite
    (E.next post-lock (Facts.append (K.path (Y.render Z.afterPromotion)) postPath))
  initialized-demote : E.Executes X.start demoteAll (Z.joined Z.demote Y.d10)
  initialized-demote = Facts.append Prefix.initialized-demotion (Facts.append (K.path (Y.render Y.d10)) demotePath)
pre-supply : Supply.Valid (E.source (Z.joined Z.pre Z.beforePromotion))
pre-supply = Inv.from-initial-supply Birth.actual-initializer (All.[] , All.[]) initialized-pre
post-supply : Supply.Valid (E.source (Z.joined Z.post Z.afterPromotion))
post-supply = Inv.from-initial-supply Birth.actual-initializer (All.[] , All.[]) initialized-post
demote-supply : Supply.Valid (E.source (Z.joined Z.demote Y.d10))
demote-supply = Inv.from-initial-supply Birth.actual-initializer (All.[] , All.[]) initialized-demote

-- The mux callback samples True before the catch entry/deactivation.
lateBefore : List E.Action
lateBefore = Prefix.beforeActions ++ (Prefix.startupActions ++
  (Prefix.protocol (P.control A.child₀ P.selectCommand) ∷ Prefix.protocol (P.control A.child₀ (P.demand 1)) ∷ Prefix.protocol (P.control A.child₀ P.sampleTracer) ∷ []))
abstract
  latePrefix : E.Executes X.start lateBefore (Y.render Y.a3)
  latePrefix = Facts.append Prefix.beforePath (Facts.append Prefix.startupPath
    (E.next Prefix.notification1 (E.next Prefix.notification2 (E.next Prefix.notification3 E.done))))

late1 : E.step (E.receive E.loopBoundary X.err) (K.atStage S.igCancelRequested false (Y.render Y.a3)) ≡ just (Z.caught Z.body Y.a3)
late1 = refl
late2 : E.step (E.run (S.scope S.deactivateIG)) (Z.caught Z.body Y.a3) ≡ just (Z.inactive Z.body Y.a3)
late2 = refl
late3 : E.step (E.run (S.scope S.flushIG)) (Z.inactive Z.body Y.a3) ≡ just (Z.flushed Z.body Y.a3)
late3 = refl
late4 : E.step (Prefix.protocol (P.control A.child₀ P.commitTracer)) (Z.flushed Z.body Y.a3) ≡ just (Z.late)
late4 = refl
late5 : E.step (E.captureSnapshot) (Z.late) ≡ just (Z.lateSnapshot)
late5 = refl
late6 : E.step (E.invokeFinal) (Z.lateSnapshot) ≡ just (Z.lateInvoked)
late6 = refl
late7 : E.step (E.returnFinal) (Z.lateInvoked) ≡ just (Z.lateReturned)
late7 = refl
late8 : E.step (E.finishFinal) (Z.lateReturned) ≡ just (Z.lateDone)
late8 = refl
late9 : E.step (E.run (S.scope S.publishIGResult)) (Z.lateDone) ≡ just (Z.latePublished)
late9 = refl
late10 : E.step (E.run (S.scope S.joinIG)) (Z.latePublished) ≡ just (Z.lateJoined)
late10 = refl
lateActions : List E.Action
lateActions =
  (E.receive E.loopBoundary X.err) ∷
  (E.run (S.scope S.deactivateIG)) ∷
  (E.run (S.scope S.flushIG)) ∷
  (Prefix.protocol (P.control A.child₀ P.commitTracer)) ∷
  (E.captureSnapshot) ∷
  (E.invokeFinal) ∷
  (E.returnFinal) ∷
  (E.finishFinal) ∷
  (E.run (S.scope S.publishIGResult)) ∷
  (E.run (S.scope S.joinIG)) ∷ []
abstract
  latePath : E.Executes (K.atStage S.igCancelRequested false (Y.render Y.a3)) lateActions (Z.lateJoined)
  latePath = E.next late1 (E.next late2 (E.next late3 (E.next late4 (E.next late5 (E.next late6 (E.next late7 (E.next late8 (E.next late9 (E.next late10 (E.done))))))))))

lateAll : List E.Action
lateAll = lateBefore ++ (K.actions ++ lateActions)
abstract
  initialized-late : E.Executes X.start lateAll Z.lateJoined
  initialized-late = Facts.append latePrefix (Facts.append (K.path (Y.render Y.a3)) latePath)
late-supply : Supply.Valid (E.source Z.lateJoined)
late-supply = Inv.from-initial-supply Birth.actual-initializer (All.[] , All.[]) initialized-late

-- An independent handler may progress while the IG final tracer is blocked.
otherProgress : E.State
otherProgress = Z.state (Y.sourceMux Y.m5 Y.messages Z.lateModel) S.igFlushed
  (record (Z.snapshotExit Z.body Y.a3) { phase = E.invoked })
other-handler-progresses : E.step (Prefix.protocol (P.control A.child₀ P.finishStart)) Z.lateInvoked ≡ just otherProgress
other-handler-progresses = refl
still-no-callback-return : E.step E.finishFinal otherProgress ≡ nothing
still-no-callback-return = refl
late-queue-retained : Shared.inboundInfo (Machine.world (core Z.lateJoined)) ≡ Y.messages
late-queue-retained = refl
late-registry-retained : IG.publishedState (E.governor Z.lateJoined) ≡ X.registeredState
late-registry-retained = refl

-- The CM writes and the PUBLISHED remote view have separate lifetimes.
pre-keeps-idle : lookup (ident 0) (heap (Z.joined Z.pre Z.beforePromotion)) ≡ just Y.idle
pre-keeps-idle = refl
post-keeps-active : lookup (ident 0) (heap (Z.joined Z.post Z.afterPromotion)) ≡ just Y.active
post-keeps-active = refl
demote-keeps-write : lookup (ident 0) (heap (Z.joined Z.demote Y.d10)) ≡ just Y.idle
demote-keeps-write = refl
demote-traces-published-warm : E.snapshot (E.exit (Z.joined Z.demote Y.d10)) ≡ (A.key₀ , E.warm) ∷ []
demote-traces-published-warm = refl
pre-archive : E.received (E.exit (Z.joined Z.pre Z.beforePromotion)) ≡ just Z.pre
pre-archive = refl
post-archive : E.received (E.exit (Z.joined Z.post Z.afterPromotion)) ≡ just Z.post
post-archive = refl
demote-archive : E.received (E.exit (Z.joined Z.demote Y.d10)) ≡ just Z.demote
demote-archive = refl
no-masked-unblocked-read : E.step (E.receive E.promoteRead X.err)
  (K.atStage S.igCancelRequested false (Y.render Y.g5)) ≡ nothing
no-masked-unblocked-read = refl
no-masked-assertion-receipt : E.step (E.receive E.demoteBoundary X.err)
  (K.atStage S.igCancelRequested false (Y.render Y.g6)) ≡ nothing
no-masked-assertion-receipt = refl
actual-promote-read-retries : Machine.advance (Machine.remoteStep Remote.transact) (core (Y.render Z.beforePromotion)) ≡ nothing
actual-promote-read-retries = refl
actual-promote-count-retries : Machine.advance (Machine.remoteStep Remote.readCounters) (core (Y.render Z.afterPromotion)) ≡ nothing
actual-promote-count-retries = refl
no-unmasked-call-resumption : Machine.advance (Machine.remoteStep Remote.returnToIG) (core (Z.joined Z.demote Y.d10)) ≡ nothing
no-unmasked-call-resumption = refl
no-whole-server-exit : E.step (E.run (S.scope S.finishServer)) (Z.joined Z.demote Y.d10) ≡ nothing
no-whole-server-exit = refl
