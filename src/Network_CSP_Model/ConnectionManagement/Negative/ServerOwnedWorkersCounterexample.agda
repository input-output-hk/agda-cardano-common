{-# OPTIONS --guardedness #-}

-- Counterexample to global handler quiescence, even with no foreign caller.
-- The admitted handler publishes a failed handshake. Its admission worker
-- consumes that result, removes the map entry, closes its socket, returns and
-- is joined. Leave the handler in its catch, before rethrow/finalization. CM
-- snapshots the empty map and collects no handler. Relays can finish while the
-- physical handler result is still unavailable. The handler was already live
-- at the snapshot: this also refutes the proposed snapshot-qualified coverage.
module ConnectionManagement.Negative.ServerOwnedWorkersCounterexample where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Empty using (⊥)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.State as Shared
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Variants.ServerOwnedWorkers as Variant

-- Fixed classifiers and no initiator protocols are enough for this witness.
classify : ErrorId → Bool
classify _ = false
capability : HandleId → ℕ → Bool
capability _ _ = false
open Variant I.bearerClosed classify using (module S; module E; module K; allJoined)
open Variant.Protocols I.bearerClosed classify capability using
  (module T; module SourceOuter; Runtime; runtime; source; owned; Event; run;
   joinWorker; advance′; Outer; outer; inner; relays; OuterAction; innerAct;
   relaysAct; outerStep; Executes; done; next; eraseOuter; eraseActions; outer-erasure)
private
  module N = Publication I.bearerClosed
  module C = Context classify
  module PS = Supervision classify

-- A genuinely empty CM and empty governor initialize every source table.
world : Shared.State
world = Shared.state A.emptyCM [] [] [] [] 0 [] [] []
c₀ : Machine.Configuration
c₀ = Machine.initial Shared.responderMode world
configuration : O.Configuration
configuration = O.initial c₀
settings : G.State
settings = G.governorState (G.targets 0 0 0) [] [] [] [] [] [] [] [] []
publication : N.State
publication = N.publicationState (N.C.catchState (N.D.deltaQState (N.R.unwinding
  (N.W.handlerExitState (N.G.shutdownState (N.M.monitorState (I.pre c₀) []) []) []) []) []) []) []
initial : T.Runtime
initial = T.runtime (K.combined (E.igExitState
  (S.serverState publication [] S.serving true S.igLive) E.emptyExit)
  (C.capture (PS.initial configuration settings))) T.empty
initializer : T.initialize (O.initial c₀) settings ≡ just initial
initializer = refl
start : Outer
start = outer (runtime initial []) (RR.initial true)

-- All labels below dispatch unchanged source actions, except the explicit join.
server : S.Action → OuterAction
server a = innerAct (run (T.dispatch (K.serverStep (E.run a))))
exit : E.Action → OuterAction
exit a = innerAct (run (T.dispatch (K.serverStep a)))
peer : PS.Action → OuterAction
peer a = innerAct (run (T.dispatch (K.peerStep a)))
scope : Scope.Action → OuterAction
scope a = peer (PS.scope a)
admit : Admission.AdmissionAction → OuterAction
admit a = server (S.run (S.runMachine (Machine.admissionStep A.w₀ a)))
consume : Handshake.HandshakeAction → OuterAction
consume a = server (S.run (S.runMachine (Machine.handshakeStep A.w₀ a)))
handler : H.Action → OuterAction
handler a = server (S.run (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run
  (N.W.run (N.G.run (N.M.run (N.P.run (N.U.run (B.handler a))))))))))))
coordinator : Close.Action → OuterAction
coordinator a = server (S.run (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run (N.W.shutdownStep a)))))))
err : ErrorId
err = errorId 777

-- Materialize the small changing components. Computing whole-runtime targets
-- recursively repeats selection/guard normalization and needlessly exhausts the
-- heap. These snapshots are still certified solely by actual executable edges.
captured : Shared.HandlerStart
captured = Shared.handlerStart (ident 0) (ident 0) (ident 0) A.key₀
lease : Shared.Lease
lease = Shared.lease A.w₀ []
binding : Shared.ConnMap
binding = Shared.insertConnection A.key₀ (ident 0) []
failed : Shared.HandshakeResult
failed = Shared.handlerError Shared.protocolViolation err
reason : Shared.DisconnectReason
reason = Shared.handshakeError Shared.protocolViolation err
reply : Shared.Completion
reply = Shared.disconnected reason

w1 : Shared.State
w1 = Shared.state (Shared.cmStore (Shared.full []) ([]) 0)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.acquireMap)) ∷ []) ([]) ((ident 0 , Shared.admitting A.w₀) ∷ []) ([]) 0 ([]) [] []

w2 : Shared.State
w2 = Shared.state (Shared.cmStore (Shared.taken A.w₀) ([]) 0)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.count lease)) ∷ []) ([]) ((ident 0 , Shared.admitting A.w₀) ∷ []) ([]) 0 ([]) [] []

w3 : Shared.State
w3 = Shared.state (Shared.cmStore (Shared.taken A.w₀) ([]) 0)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.prepare lease)) ∷ []) ([]) ((ident 0 , Shared.admitting A.w₀) ∷ []) ([]) 0 ([]) [] []

w4 : Shared.State
w4 = Shared.state (Shared.cmStore (Shared.taken A.w₀) ([]) 0)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.selectEntry lease (ident 0))) ∷ []) ([]) ((ident 0 , Shared.admitting A.w₀) ∷ []) (ident 0 ∷ []) 1 ([]) [] []

w5 : Shared.State
w5 = Shared.state (Shared.cmStore (Shared.taken A.w₀) ((ident 0 , Shared.unnegotiated inbound A.key₀ A.child₀) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.forkHandler lease (ident 0) (ident 0))) ∷ []) ([]) ((ident 0 , Shared.admitting A.w₀) ∷ []) (ident 0 ∷ []) 1 ([]) [] []

w6 : Shared.State
w6 = Shared.state (Shared.cmStore (Shared.taken A.w₀) ((ident 0 , Shared.unnegotiated inbound A.key₀ A.child₀) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.publish lease (ident 0) (ident 0))) ∷ []) ((A.child₀ , captured) ∷ []) ((ident 0 , Shared.handling A.child₀) ∷ []) (ident 0 ∷ []) 1 ([]) [] []

w7 : Shared.State
w7 = Shared.state (Shared.cmStore (Shared.full binding) ((ident 0 , Shared.unnegotiated inbound A.key₀ A.child₀) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.countPublished (ident 0) (ident 0))) ∷ []) ((A.child₀ , captured) ∷ []) ((ident 0 , Shared.handling A.child₀) ∷ []) (ident 0 ∷ []) 1 ([]) [] []

w8 : Shared.State
w8 = Shared.state (Shared.cmStore (Shared.full binding) ((ident 0 , Shared.unnegotiated inbound A.key₀ A.child₀) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.awaitHandshake (ident 0) (ident 0))) ∷ []) ((A.child₀ , captured) ∷ []) ((ident 0 , Shared.handling A.child₀) ∷ []) (ident 0 ∷ []) 1 ([]) [] []

w11 : Shared.State
w11 = Shared.state (Shared.cmStore (Shared.full binding) ((ident 0 , Shared.unnegotiated inbound A.key₀ A.child₀) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.awaitHandshake (ident 0) (ident 0))) ∷ []) ((A.child₀ , captured) ∷ []) ((ident 0 , Shared.handling A.child₀) ∷ []) (ident 0 ∷ []) 1 ((ident 0 , failed) ∷ []) [] []

w12 : Shared.State
w12 = Shared.state (Shared.cmStore (Shared.full binding) ((ident 0 , Shared.unnegotiated inbound A.key₀ A.child₀) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.commitHandshake (ident 0) failed)) ∷ []) ((A.child₀ , captured) ∷ []) ((ident 0 , Shared.handling A.child₀) ∷ []) (ident 0 ∷ []) 1 ((ident 0 , failed) ∷ []) [] []

w13 : Shared.State
w13 = Shared.state (Shared.cmStore (Shared.full []) ((ident 0 , Shared.terminated (just err)) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.countHandshake reply)) ∷ []) ((A.child₀ , captured) ∷ []) ((ident 0 , Shared.handling A.child₀) ∷ []) (ident 0 ∷ []) 1 ((ident 0 , failed) ∷ []) [] []

w14 : Shared.State
w14 = Shared.state (Shared.cmStore (Shared.full []) ((ident 0 , Shared.terminated (just err)) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.returnHandshake reply)) ∷ []) ((A.child₀ , captured) ∷ []) ((ident 0 , Shared.handling A.child₀) ∷ []) (ident 0 ∷ []) 1 ((ident 0 , failed) ∷ []) [] []

w15 : Shared.State
w15 = Shared.state (Shared.cmStore (Shared.full []) ((ident 0 , Shared.terminated (just err)) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.completedHandshake reply)) ∷ []) ((A.child₀ , captured) ∷ []) ((ident 0 , Shared.handling A.child₀) ∷ []) (ident 0 ∷ []) 1 ((ident 0 , failed) ∷ []) [] []

w17 : Shared.State
w17 = Shared.state (Shared.cmStore (Shared.full []) ((ident 0 , Shared.terminated (just err)) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.completedHandshake reply)) ∷ []) ((A.child₀ , captured) ∷ []) ((ident 0 , Shared.closed) ∷ []) (ident 0 ∷ []) 1 ((ident 0 , failed) ∷ []) [] []

-- Rebuild only the unchanged wrappers around explicit component values.
threads : Maybe H.Phase → Store WorkerId H.Thread
threads nothing = []
threads (just pc) = (A.child₀ , H.handlerThread captured pc) ∷ []
origins : Maybe H.Phase → Store WorkerId Provenance
origins nothing = []
origins (just _) = (A.child₀ , inbound) ∷ []
rawWorkers : Maybe S.WorkerPC → Store WorkerId S.Worker
rawWorkers nothing = []
rawWorkers (just pc) = (A.w₀ , S.rawWorker A.r₀ pc 0) ∷ []
-- The one close has happened in the bodyExited/resultAvailable snapshots.
closedWorkers : S.WorkerPC → Store WorkerId S.Worker
closedWorkers pc = (A.w₀ , S.rawWorker A.r₀ pc 1) ∷ []
k₀ : C.Context
k₀ = C.capture (PS.initial configuration settings)
igInactive igFlushed : IG.Runtime
igInactive = record IG.initial { continuation = IG.exitFlush; execution = record (IG.execution IG.initial) { active = false } }
igFlushed = record igInactive { continuation = IG.exited }
received : E.Receipt
received = E.receipt E.loopBoundary err nothing
caught : E.Exit
caught = E.caughtExit received
traversing : E.Exit
traversing = record caught { phase = E.traversing }
bodyDone : E.Exit
bodyDone = record traversing { phase = E.bodyDone }
resultDone : E.Exit
resultDone = record bodyDone { result = just (S.async err) }

render : Shared.State → Maybe H.Phase → Store WorkerId S.Worker → Variant.Ownership I.bearerClosed classify →
  C.Context → S.Stage → Bool → S.IGPhase → E.Exit → IG.Runtime → Close.State → RR.State → Outer
render world phase workers handles context stage listener igPhase e governor coord r = outer
  (runtime (T.runtime (K.combined (E.igExitState (S.serverState n workers stage listener igPhase) e) context) T.empty) handles) r
  where
  core = record c₀ { world = world; inboundGovernor = governor }
  physical = N.P.protocolState (N.U.supervised (B.supervised (O.initial core) (threads phase) coord) (origins phase) []) [] []
  n = N.publicationState (N.C.catchState (N.D.deltaQState (N.R.unwinding
    (N.W.handlerExitState (N.G.shutdownState (N.M.monitorState physical []) []) []) []) []) []) []

s0 : Outer
s0 = start

-- Explicit target, certified by the source-reusing executable transition.
a1 : OuterAction
a1 = server (S.acceptedFork A.w₀ A.r₀)
s1 : Outer
s1 = render w1 (nothing) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e1 : outerStep a1 s0 ≡ just s1
e1 = refl

-- Explicit target, certified by the source-reusing executable transition.
a2 : OuterAction
a2 = admit Admission.take
s2 : Outer
s2 = render w2 (nothing) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e2 : outerStep a2 s1 ≡ just s2
e2 = refl

-- Explicit target, certified by the source-reusing executable transition.
a3 : OuterAction
a3 = admit Admission.countLimit
s3 : Outer
s3 = render w3 (nothing) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e3 : outerStep a3 s2 ≡ just s3
e3 = refl

-- Explicit target, certified by the source-reusing executable transition.
a4 : OuterAction
a4 = admit Admission.allocatePromise
s4 : Outer
s4 = render w4 (nothing) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e4 : outerStep a4 s3 ≡ just s4
e4 = refl

-- Explicit target, certified by the source-reusing executable transition.
a5 : OuterAction
a5 = admit Admission.chooseEntry
s5 : Outer
s5 = render w5 (nothing) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e5 : outerStep a5 s4 ≡ just s5
e5 = refl

-- Explicit target, certified by the source-reusing executable transition.
a6 : OuterAction
a6 = admit Admission.fork
s6 : Outer
s6 = render w6 (just H.maskedSetup) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e6 : outerStep a6 s5 ≡ just s6
e6 = refl

-- Explicit target, certified by the source-reusing executable transition.
a7 : OuterAction
a7 = admit Admission.putMapBack
s7 : Outer
s7 = render w7 (just H.maskedSetup) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e7 : outerStep a7 s6 ≡ just s7
e7 = refl

-- Explicit target, certified by the source-reusing executable transition.
a8 : OuterAction
a8 = admit Admission.readCounters
s8 : Outer
s8 = render w8 (just H.maskedSetup) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e8 : outerStep a8 s7 ≡ just s8
e8 = refl

-- Explicit target, certified by the source-reusing executable transition.
a9 : OuterAction
a9 = handler (H.enterHandshake A.child₀)
s9 : Outer
s9 = render w8 (just H.handshaking) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e9 : outerStep a9 s8 ≡ just s9
e9 = refl

-- Explicit target, certified by the source-reusing executable transition.
a10 : OuterAction
a10 = handler (H.deliverHandshakeCancellation A.child₀ err)
s10 : Outer
s10 = render w8 (just (H.caughtCancellation err)) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e10 : outerStep a10 s9 ≡ just s10
e10 = refl

-- Explicit target, certified by the source-reusing executable transition.
a11 : OuterAction
a11 = handler (H.publishCaught A.child₀)
s11 : Outer
s11 = render w11 (just (H.cancellationPublished err)) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e11 : outerStep a11 s10 ≡ just s11
e11 = refl

-- Explicit target, certified by the source-reusing executable transition.
a12 : OuterAction
a12 = consume Handshake.readResult
s12 : Outer
s12 = render w12 (just (H.cancellationPublished err)) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e12 : outerStep a12 s11 ≡ just s12
e12 = refl

-- Explicit target, certified by the source-reusing executable transition.
a13 : OuterAction
a13 = consume Handshake.commitResult
s13 : Outer
s13 = render w13 (just (H.cancellationPublished err)) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e13 : outerStep a13 s12 ≡ just s13
e13 = refl

-- Explicit target, certified by the source-reusing executable transition.
a14 : OuterAction
a14 = consume Handshake.readResultCounters
s14 : Outer
s14 = render w14 (just (H.cancellationPublished err)) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e14 : outerStep a14 s13 ≡ just s14
e14 = refl

-- Explicit target, certified by the source-reusing executable transition.
a15 : OuterAction
a15 = consume Handshake.returnResult
s15 : Outer
s15 = render w15 (just (H.cancellationPublished err)) (rawWorkers (just S.calling)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e15 : outerStep a15 s14 ≡ just s15
e15 = refl

-- Explicit target, certified by the source-reusing executable transition.
a16 : OuterAction
a16 = server (S.workerReturned A.w₀)
s16 : Outer
s16 = render w15 (just (H.cancellationPublished err)) (rawWorkers (just S.closeDisconnected)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e16 : outerStep a16 s15 ≡ just s16
e16 = refl

-- Explicit target, certified by the source-reusing executable transition.
a17 : OuterAction
a17 = server (S.workerClose A.w₀ nothing)
s17 : Outer
s17 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.bodyExited S.returned)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e17 : outerStep a17 s16 ≡ just s17
e17 = refl

-- Explicit target, certified by the source-reusing executable transition.
a18 : OuterAction
a18 = server (S.workerResult A.w₀)
s18 : Outer
s18 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e18 : outerStep a18 s17 ≡ just s18
e18 = refl

-- Explicit target, certified by the source-reusing executable transition.
a19 : OuterAction
a19 = innerAct (joinWorker A.w₀)
s19 : Outer
s19 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e19 : outerStep a19 s18 ≡ just s19
e19 = refl

-- The actual small scope/pool fields written by this edge.
k20 : C.Context
k20 = record k₀
  { scopes = Scope.scopeState Scope.running Scope.running Scope.running Scope.running (Scope.closing Scope.churn) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a20 : OuterAction
a20 = scope Scope.beginUnwind
s20 : Outer
s20 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k20 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e20 : outerStep a20 s19 ≡ just s20
e20 = refl

-- The actual small scope/pool fields written by this edge.
k21 : C.Context
k21 = record k₀
  { scopes = Scope.scopeState Scope.cancelRequested Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a21 : OuterAction
a21 = scope Scope.requestCancel
s21 : Outer
s21 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k21 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e21 : outerStep a21 s20 ≡ just s21
e21 = refl

-- The actual small scope/pool fields written by this edge.
k22 : C.Context
k22 = record k₀
  { scopes = Scope.scopeState Scope.cancelDelivered Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a22 : OuterAction
a22 = scope Scope.deliverCancel
s22 : Outer
s22 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k22 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e22 : outerStep a22 s21 ≡ just s22
e22 = refl

-- The actual small scope/pool fields written by this edge.
k23 : C.Context
k23 = record k₀
  { scopes = Scope.scopeState Scope.bodyExited Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a23 : OuterAction
a23 = scope (Scope.bodyExit Scope.churn)
s23 : Outer
s23 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k23 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e23 : outerStep a23 s22 ≡ just s23
e23 = refl

-- The actual small scope/pool fields written by this edge.
k24 : C.Context
k24 = record k₀
  { scopes = Scope.scopeState Scope.resultAvailable Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a24 : OuterAction
a24 = scope (Scope.publishResult Scope.churn)
s24 : Outer
s24 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k24 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e24 : outerStep a24 s23 ≡ just s24
e24 = refl

-- The actual small scope/pool fields written by this edge.
k25 : C.Context
k25 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.running Scope.running Scope.running (Scope.closing Scope.governor) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a25 : OuterAction
a25 = scope Scope.join
s25 : Outer
s25 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k25 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e25 : outerStep a25 s24 ≡ just s25
e25 = refl

-- The actual small scope/pool fields written by this edge.
k26 : C.Context
k26 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.cancelRequested Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a26 : OuterAction
a26 = scope Scope.requestCancel
s26 : Outer
s26 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k26 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e26 : outerStep a26 s25 ≡ just s26
e26 = refl

-- The actual small scope/pool fields written by this edge.
k27 : C.Context
k27 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.cancelDelivered Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a27 : OuterAction
a27 = scope Scope.deliverCancel
s27 : Outer
s27 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k27 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e27 : outerStep a27 s26 ≡ just s27
e27 = refl

-- The actual small scope/pool fields written by this edge.
k28 : C.Context
k28 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.cancelDelivered Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closing }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a28 : OuterAction
a28 = peer (PS.run (PS.GP.beginClose []))
s28 : Outer
s28 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k28 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e28 : outerStep a28 s27 ≡ just s28
e28 = refl

-- The actual small scope/pool fields written by this edge.
k29 : C.Context
k29 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.cancelDelivered Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a29 : OuterAction
a29 = peer (PS.run PS.GP.finishClose)
s29 : Outer
s29 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k29 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e29 : outerStep a29 s28 ≡ just s29
e29 = refl

-- The actual small scope/pool fields written by this edge.
k30 : C.Context
k30 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.bodyExited Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a30 : OuterAction
a30 = scope (Scope.bodyExit Scope.governor)
s30 : Outer
s30 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k30 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e30 : outerStep a30 s29 ≡ just s30
e30 = refl

-- The actual small scope/pool fields written by this edge.
k31 : C.Context
k31 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.resultAvailable Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a31 : OuterAction
a31 = scope (Scope.publishResult Scope.governor)
s31 : Outer
s31 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k31 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e31 : outerStep a31 s30 ≡ just s31
e31 = refl

-- The actual small scope/pool fields written by this edge.
k32 : C.Context
k32 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.running Scope.running (Scope.closing Scope.localRoot) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a32 : OuterAction
a32 = scope Scope.join
s32 : Outer
s32 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k32 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e32 : outerStep a32 s31 ≡ just s32
e32 = refl

-- The actual small scope/pool fields written by this edge.
k33 : C.Context
k33 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.cancelRequested Scope.running (Scope.closing Scope.localRoot) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a33 : OuterAction
a33 = scope Scope.requestCancel
s33 : Outer
s33 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k33 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e33 : outerStep a33 s32 ≡ just s33
e33 = refl

-- The actual small scope/pool fields written by this edge.
k34 : C.Context
k34 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.cancelDelivered Scope.running (Scope.closing Scope.localRoot) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a34 : OuterAction
a34 = scope Scope.deliverCancel
s34 : Outer
s34 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k34 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e34 : outerStep a34 s33 ≡ just s34
e34 = refl

-- The actual small scope/pool fields written by this edge.
k35 : C.Context
k35 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.bodyExited Scope.running (Scope.closing Scope.localRoot) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a35 : OuterAction
a35 = scope (Scope.bodyExit Scope.localRoot)
s35 : Outer
s35 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k35 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e35 : outerStep a35 s34 ≡ just s35
e35 = refl

-- The actual small scope/pool fields written by this edge.
k36 : C.Context
k36 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.resultAvailable Scope.running (Scope.closing Scope.localRoot) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a36 : OuterAction
a36 = scope (Scope.publishResult Scope.localRoot)
s36 : Outer
s36 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k36 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e36 : outerStep a36 s35 ≡ just s36
e36 = refl

-- The actual small scope/pool fields written by this edge.
k37 : C.Context
k37 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.running (Scope.closing Scope.ledger) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a37 : OuterAction
a37 = scope Scope.join
s37 : Outer
s37 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k37 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e37 : outerStep a37 s36 ≡ just s37
e37 = refl

-- The actual small scope/pool fields written by this edge.
k38 : C.Context
k38 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.cancelRequested (Scope.closing Scope.ledger) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a38 : OuterAction
a38 = scope Scope.requestCancel
s38 : Outer
s38 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k38 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e38 : outerStep a38 s37 ≡ just s38
e38 = refl

-- The actual small scope/pool fields written by this edge.
k39 : C.Context
k39 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.cancelDelivered (Scope.closing Scope.ledger) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a39 : OuterAction
a39 = scope Scope.deliverCancel
s39 : Outer
s39 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k39 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e39 : outerStep a39 s38 ≡ just s39
e39 = refl

-- The actual small scope/pool fields written by this edge.
k40 : C.Context
k40 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.bodyExited (Scope.closing Scope.ledger) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a40 : OuterAction
a40 = scope (Scope.bodyExit Scope.ledger)
s40 : Outer
s40 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k40 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e40 : outerStep a40 s39 ≡ just s40
e40 = refl

-- The actual small scope/pool fields written by this edge.
k41 : C.Context
k41 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.resultAvailable (Scope.closing Scope.ledger) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a41 : OuterAction
a41 = scope (Scope.publishResult Scope.ledger)
s41 : Outer
s41 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k41 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e41 : outerStep a41 s40 ≡ just s41
e41 = refl

-- The actual small scope/pool fields written by this edge.
k42 : C.Context
k42 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.readyToFinish) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a42 : OuterAction
a42 = scope Scope.join
s42 : Outer
s42 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k42 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e42 : outerStep a42 s41 ≡ just s42
e42 = refl

-- The actual small scope/pool fields written by this edge.
k43 : C.Context
k43 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

-- Explicit target, certified by the source-reusing executable transition.
a43 : OuterAction
a43 = scope Scope.finishClose
s43 : Outer
s43 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k43 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e43 : outerStep a43 s42 ≡ just s43
e43 = refl

-- The actual small scope/pool fields written by this edge.
k44 : C.Context
k44 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closing } }

-- Explicit target, certified by the source-reusing executable transition.
a44 : OuterAction
a44 = peer (PS.beginMonitorClose [])
s44 : Outer
s44 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k44 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e44 : outerStep a44 s43 ≡ just s44
e44 = refl

-- The actual small scope/pool fields written by this edge.
k45 : C.Context
k45 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a45 : OuterAction
a45 = peer PS.finishMonitorClose
s45 : Outer
s45 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k45 S.serving true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e45 : outerStep a45 s44 ≡ just s45
e45 = refl

-- The actual small scope/pool fields written by this edge.
k46 : C.Context
k46 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a46 : OuterAction
a46 = server (S.scope S.returnAction)
s46 : Outer
s46 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k46 S.actionBodyExited true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e46 : outerStep a46 s45 ≡ just s46
e46 = refl

-- The actual small scope/pool fields written by this edge.
k47 : C.Context
k47 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a47 : OuterAction
a47 = server (S.scope S.publishActionResult)
s47 : Outer
s47 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k47 S.actionResultAvailable true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e47 : outerStep a47 s46 ≡ just s47
e47 = refl

-- The actual small scope/pool fields written by this edge.
k48 : C.Context
k48 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a48 : OuterAction
a48 = server (S.scope S.selectActionWinner)
s48 : Outer
s48 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k48 S.closingAccept true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e48 : outerStep a48 s47 ≡ just s48
e48 = refl

-- The actual small scope/pool fields written by this edge.
k49 : C.Context
k49 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a49 : OuterAction
a49 = server (S.scope S.requestAcceptCancel)
s49 : Outer
s49 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k49 S.acceptCancelRequested true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e49 : outerStep a49 s48 ≡ just s49
e49 = refl

-- The actual small scope/pool fields written by this edge.
k50 : C.Context
k50 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a50 : OuterAction
a50 = server (S.scope S.deliverAcceptAtWait)
s50 : Outer
s50 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k50 S.acceptCancelDelivered true S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e50 : outerStep a50 s49 ≡ just s50
e50 = refl

-- The actual small scope/pool fields written by this edge.
k51 : C.Context
k51 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a51 : OuterAction
a51 = server (S.scope S.closeListener)
s51 : Outer
s51 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k51 S.acceptBodyExited false S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e51 : outerStep a51 s50 ≡ just s51
e51 = refl

-- The actual small scope/pool fields written by this edge.
k52 : C.Context
k52 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a52 : OuterAction
a52 = server (S.scope S.publishAcceptResult)
s52 : Outer
s52 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k52 S.acceptResultAvailable false S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e52 : outerStep a52 s51 ≡ just s52
e52 = refl

-- The actual small scope/pool fields written by this edge.
k53 : C.Context
k53 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a53 : OuterAction
a53 = server (S.scope S.joinAccept)
s53 : Outer
s53 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k53 S.acceptJoined false S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e53 : outerStep a53 s52 ≡ just s53
e53 = refl

-- The actual small scope/pool fields written by this edge.
k54 : C.Context
k54 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a54 : OuterAction
a54 = server (S.scope S.traceStopped)
s54 : Outer
s54 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k54 S.serverStopped false S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e54 : outerStep a54 s53 ≡ just s54
e54 = refl

-- The actual small scope/pool fields written by this edge.
k55 : C.Context
k55 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a55 : OuterAction
a55 = server (S.scope S.cancelJoinReturnedAction)
s55 : Outer
s55 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k55 S.actionJoined false S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e55 : outerStep a55 s54 ≡ just s55
e55 = refl

-- The actual small scope/pool fields written by this edge.
k56 : C.Context
k56 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a56 : OuterAction
a56 = server (S.scope S.requestIGCancel)
s56 : Outer
s56 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k56 S.igCancelRequested false S.igLive E.emptyExit IG.initial (Close.initialState) (RR.initial true)
e56 : outerStep a56 s55 ≡ just s56
e56 = refl

-- The actual small scope/pool fields written by this edge.
k57 : C.Context
k57 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a57 : OuterAction
a57 = exit (E.receive E.loopBoundary err)
s57 : Outer
s57 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k57 S.igCancelRequested false S.igCaught caught IG.initial (Close.initialState) (RR.initial true)
e57 : outerStep a57 s56 ≡ just s57
e57 = refl

-- The actual small scope/pool fields written by this edge.
k58 : C.Context
k58 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a58 : OuterAction
a58 = server (S.scope S.deactivateIG)
s58 : Outer
s58 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k58 S.igCancelRequested false S.igInactive caught igInactive (Close.initialState) (RR.initial true)
e58 : outerStep a58 s57 ≡ just s58
e58 = refl

-- The actual small scope/pool fields written by this edge.
k59 : C.Context
k59 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a59 : OuterAction
a59 = server (S.scope S.flushIG)
s59 : Outer
s59 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k59 S.igCancelRequested false S.igFlushed caught igFlushed (Close.initialState) (RR.initial true)
e59 : outerStep a59 s58 ≡ just s59
e59 = refl

-- The actual small scope/pool fields written by this edge.
k60 : C.Context
k60 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a60 : OuterAction
a60 = exit E.captureSnapshot
s60 : Outer
s60 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k60 S.igCancelRequested false S.igFlushed traversing igFlushed (Close.initialState) (RR.initial true)
e60 : outerStep a60 s59 ≡ just s60
e60 = refl

-- The actual small scope/pool fields written by this edge.
k61 : C.Context
k61 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a61 : OuterAction
a61 = exit E.finishFinal
s61 : Outer
s61 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k61 S.igCancelRequested false S.igBodyExited bodyDone igFlushed (Close.initialState) (RR.initial true)
e61 : outerStep a61 s60 ≡ just s61
e61 = refl

-- The actual small scope/pool fields written by this edge.
k62 : C.Context
k62 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a62 : OuterAction
a62 = server (S.scope S.publishIGResult)
s62 : Outer
s62 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k62 S.igCancelRequested false S.igResultAvailable resultDone igFlushed (Close.initialState) (RR.initial true)
e62 : outerStep a62 s61 ≡ just s62
e62 = refl

-- The actual small scope/pool fields written by this edge.
k63 : C.Context
k63 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a63 : OuterAction
a63 = server (S.scope S.joinIG)
s63 : Outer
s63 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k63 S.igJoined false S.igResultAvailable resultDone igFlushed (Close.initialState) (RR.initial true)
e63 : outerStep a63 s62 ≡ just s63
e63 = refl

-- The actual small scope/pool fields written by this edge.
k64 : C.Context
k64 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a64 : OuterAction
a64 = server (S.scope S.beginCM)
s64 : Outer
s64 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k64 S.closingCM false S.igResultAvailable resultDone igFlushed (Close.initialState) (RR.initial true)
e64 : outerStep a64 s63 ≡ just s64
e64 = refl

-- The actual small scope/pool fields written by this edge.
k65 : C.Context
k65 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a65 : OuterAction
a65 = coordinator Close.captureSnapshot
s65 : Outer
s65 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k65 S.closingCM false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.reading [] [] []) (RR.initial true)
e65 : outerStep a65 s64 ≡ just s65
e65 = refl

-- The actual small scope/pool fields written by this edge.
k66 : C.Context
k66 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a66 : OuterAction
a66 = coordinator Close.finishTraversal
s66 : Outer
s66 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k66 S.closingCM false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
e66 : outerStep a66 s65 ≡ just s66
e66 = refl

-- The actual small scope/pool fields written by this edge.
k67 : C.Context
k67 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a67 : OuterAction
a67 = coordinator Close.finishClose
s67 : Outer
s67 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k67 S.closingCM false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.closed [] [] []) (RR.initial true)
e67 : outerStep a67 s66 ≡ just s67
e67 = refl

-- The actual small scope/pool fields written by this edge.
k68 : C.Context
k68 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a68 : OuterAction
a68 = server (S.scope S.finishServer)
s68 : Outer
s68 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k68 S.serverReturned false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.closed [] [] []) (RR.initial true)
e68 : outerStep a68 s67 ≡ just s68
e68 = refl

-- The actual small scope/pool fields written by this edge.
k69 : C.Context
k69 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a69 : OuterAction
a69 = relaysAct RR.requestCancel
s69 : Outer
s69 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k69 S.serverReturned false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.cancelRequested) RR.cancelling)
e69 : outerStep a69 s68 ≡ just s69
e69 = refl

-- The actual small scope/pool fields written by this edge.
k70 : C.Context
k70 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a70 : OuterAction
a70 = relaysAct (RR.threadAct RR.deliverCancel)
s70 : Outer
s70 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k70 S.serverReturned false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.cancelDelivered) RR.cancelling)
e70 : outerStep a70 s69 ≡ just s70
e70 = refl

-- The actual small scope/pool fields written by this edge.
k71 : C.Context
k71 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a71 : OuterAction
a71 = relaysAct (RR.threadAct RR.bodyExit)
s71 : Outer
s71 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k71 S.serverReturned false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.bodyExited) RR.cancelling)
e71 : outerStep a71 s70 ≡ just s71
e71 = refl

-- The actual small scope/pool fields written by this edge.
k72 : C.Context
k72 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a72 : OuterAction
a72 = relaysAct (RR.threadAct RR.publishResult)
s72 : Outer
s72 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k72 S.serverReturned false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.resultAvailable) RR.cancelling)
e72 : outerStep a72 s71 ≡ just s72
e72 = refl

-- The actual small scope/pool fields written by this edge.
k73 : C.Context
k73 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a73 : OuterAction
a73 = relaysAct (RR.threadAct RR.join)
s73 : Outer
s73 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k73 S.serverReturned false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.joined) RR.cancelling)
e73 : outerStep a73 s72 ≡ just s73
e73 = refl

-- The actual small scope/pool fields written by this edge.
k74 : C.Context
k74 = record k₀
  { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

-- Explicit target, certified by the source-reusing executable transition.
a74 : OuterAction
a74 = relaysAct RR.finish
s74 : Outer
s74 = render w17 (just (H.cancellationPublished err)) (closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) k74 S.serverReturned false S.igResultAvailable resultDone igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.joined) RR.finished)
e74 : outerStep a74 s73 ≡ just s74
e74 = refl

actions : List OuterAction
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ a19 ∷ a20 ∷ a21 ∷ a22 ∷ a23 ∷ a24 ∷ a25 ∷ a26 ∷ a27 ∷ a28 ∷ a29 ∷ a30 ∷ a31 ∷ a32 ∷ a33 ∷ a34 ∷ a35 ∷ a36 ∷ a37 ∷ a38 ∷ a39 ∷ a40 ∷ a41 ∷ a42 ∷ a43 ∷ a44 ∷ a45 ∷ a46 ∷ a47 ∷ a48 ∷ a49 ∷ a50 ∷ a51 ∷ a52 ∷ a53 ∷ a54 ∷ a55 ∷ a56 ∷ a57 ∷ a58 ∷ a59 ∷ a60 ∷ a61 ∷ a62 ∷ a63 ∷ a64 ∷ a65 ∷ a66 ∷ a67 ∷ a68 ∷ a69 ∷ a70 ∷ a71 ∷ a72 ∷ a73 ∷ a74 ∷ []

-- Every edge is checked by computation, with one actual admitted/joined worker.
abstract
  counterexample-run : Executes start actions s74
  counterexample-run = next e1 (next e2 (next e3 (next e4 (next e5 (next e6 (next e7 (next e8 (next e9 (next e10 (next e11 (next e12 (next e13 (next e14 (next e15 (next e16 (next e17 (next e18 (next e19 (next e20 (next e21 (next e22 (next e23 (next e24 (next e25 (next e26 (next e27 (next e28 (next e29 (next e30 (next e31 (next e32 (next e33 (next e34 (next e35 (next e36 (next e37 (next e38 (next e39 (next e40 (next e41 (next e42 (next e43 (next e44 (next e45 (next e46 (next e47 (next e48 (next e49 (next e50 (next e51 (next e52 (next e53 (next e54 (next e55 (next e56 (next e57 (next e58 (next e59 (next e60 (next e61 (next e62 (next e63 (next e64 (next e65 (next e66 (next e67 (next e68 (next e69 (next e70 (next e71 (next e72 (next e73 (next e74 (done))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- Read the same physical registry/oracle used by the real CM wrapper.
serverOf : Outer → S.State
serverOf s = E.base (K.server (T.base (source (inner s))))
physical : Outer → N.W.State
physical s = N.R.base (N.raw (S.base (serverOf s)))
coord : Outer → Close.State
coord s = N.W.shutdown (physical s)

-- The worker is actually joined before the snapshot, with an available result.
worker-joined-before-snapshot : lookup A.w₀ (owned (inner s64)) ≡ just true
worker-joined-before-snapshot = refl
worker-result-before-snapshot : S.resultOf A.w₀ (serverOf s64) ≡ just S.returned
worker-result-before-snapshot = refl

-- The failed handshake's consumer removed the map binding, before handler exit.
empty-map-at-snapshot : Shared.mapCell (Shared.cm (S.shared (serverOf s64))) ≡ Shared.full []
empty-map-at-snapshot = refl
unavailable-at-snapshot : N.W.resultReady A.child₀ (physical s65) ≡ false
unavailable-at-snapshot = refl
empty-snapshot : Close.snapshot (coord s65) ≡ []
empty-snapshot = refl

-- Relays are finished, and every historical admission handle has been joined.
finished-relays : relays s74 ≡ RR.relaysState (just RR.joined) RR.finished
finished-relays = refl
all-workers-joined : allJoined (owned (inner s74)) ≡ true
all-workers-joined = refl
no-foreign-acquire : O.acquiring (T.sourceOf (source (inner s74))) ≡ []
no-foreign-acquire = refl
no-foreign-release : O.releasing (T.sourceOf (source (inner s74))) ≡ []
no-foreign-release = refl
closed-empty-coordinator : coord s74 ≡ Close.shutdownState Close.closed [] [] []
closed-empty-coordinator = refl

-- The same exact physical handler is still in its catch before rethrow.
live-handler : lookup A.child₀ (B.threads (N.W.physical (physical s74))) ≡
  just (H.handlerThread (Shared.handlerStart (ident 0) (Shared.socketRef A.r₀) (ident 0) (Shared.key A.r₀))
    (H.cancellationPublished err))
live-handler = refl
unavailable-at-end : N.W.resultReady A.child₀ (physical s74) ≡ false
unavailable-at-end = refl

-- Membership is required only for an existing physical thread with an
-- unavailable result; absence from the registry alone is not called liveness.
open import Data.List.Membership.Propositional using (_∈_)
LiveCovered : Outer → Set
LiveCovered s = ∀ w h → lookup w (B.threads (N.W.physical (physical s))) ≡ just h →
  N.W.resultReady w (physical s) ≡ false → w ∈ Close.collected (coord s)

-- The handler has this same live physical continuation already at the snapshot.
live-at-snapshot : lookup A.child₀ (B.threads (N.W.physical (physical s65))) ≡
  just (H.handlerThread captured (H.cancellationPublished err))
live-at-snapshot = refl

-- The final counterexample refutes the live-handler conjunct, not join progress.
not-quiescent : LiveCovered s74 → ⊥
not-quiescent covered = case covered A.child₀ _ live-handler unavailable-at-end of λ ()

-- Exact initialized/finished universal target, refuted at these fixed classifiers.
no-universal-quiescence :
  (∀ {c g begin as final} → T.initialize (O.initial c) g ≡ just begin →
    Executes (outer (runtime begin []) (RR.initial true)) as final →
    RR.owner (relays final) ≡ RR.finished → LiveCovered final) → ⊥
no-universal-quiescence claim = not-quiescent (claim initializer counterexample-run refl)
