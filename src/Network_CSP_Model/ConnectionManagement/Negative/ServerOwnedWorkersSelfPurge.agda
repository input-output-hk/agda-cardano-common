{-# OPTIONS --guardedness #-}

-- Initialized successful admission, followed by ordinary handler self-purge.
-- The admission worker returns Connected and is joined before the handler's
-- synchronous buffer-acquisition failure. Cleanup closes its socket and purges
-- the map, then pauses at cleanupCount. Map-based CM and relays can finish with
-- this physical handler still live. No admission-worker or handler cancellation.
module ConnectionManagement.Negative.ServerOwnedWorkersSelfPurge where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe; maybe)
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
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.MuxRuntime
import ConnectionManagement.Rules.HandlerLifecycle as Life
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


-- Only small source components are computed; wrapper targets are flat.
captured : Shared.HandlerStart
captured = Shared.handlerStart (ident 0) (ident 0) (ident 0) A.key₀
runU : N.U.Action → OuterAction
runU a = server (S.run (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run
  (N.W.run (N.G.run (N.M.run (N.P.run a))))))))))
runR : N.R.Action → OuterAction
runR a = server (S.run (N.run (N.C.run (N.D.run a))))
runW : N.W.Action → OuterAction
runW a = runR (N.R.run (N.D.X.run a))
-- Empty protocols suffice for negotiation and an installed mux identity.
frame : N.U.Progress → N.S.State → N.U.Frame
frame p st = N.U.frame captured inbound [] duplex p st N.U.setupPending
fault : N.R.PC → N.R.Fault
fault pc = N.R.fault captured (ident 0) N.S.published
  ConnectionManagement.Rules.MuxRuntime.returned N.R.beforeBuffer (N.R.sync err) pc

-- Rebuild independent physical and source fields, retaining the real exit PC.
render : Machine.Configuration → Maybe H.Phase → Maybe N.U.Frame → Maybe N.R.PC → Maybe N.W.Phase →
  Store WorkerId S.Worker → Variant.Ownership I.bearerClosed classify →
  C.Context → S.Stage → Bool → S.IGPhase → E.Exit → Close.State → RR.State → Outer
render core hp uf rp wp workers handles context stage listener igPhase e coord r = outer
  (runtime (T.runtime (K.combined (E.igExitState
    (S.serverState n workers stage listener igPhase) e) context) T.empty) handles) r
  where
  th = Data.Maybe.maybe (λ p → (A.child₀ , H.handlerThread captured p) ∷ []) [] hp
  ori = Data.Maybe.maybe (λ _ → (A.child₀ , inbound) ∷ []) [] hp
  fs = Data.Maybe.maybe (λ f → (A.child₀ , f) ∷ []) [] uf
  rs = Data.Maybe.maybe (λ p → (A.child₀ , fault p) ∷ []) [] rp
  ws = Data.Maybe.maybe (λ p → (A.child₀ , N.W.exitFrame captured p nothing) ∷ []) [] wp
  physical = N.P.protocolState (N.U.supervised (B.supervised (O.initial core) th coord) ori fs) [] []
  n = N.publicationState (N.C.catchState (N.D.deltaQState (N.R.unwinding
    (N.W.handlerExitState (N.G.shutdownState (N.M.monitorState physical []) []) ws) rs) []) []) []
k₀ : C.Context
k₀ = C.capture (PS.initial configuration settings)
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

lease : Shared.Lease
lease = Shared.lease A.w₀ []
binding : Shared.ConnMap
binding = Shared.insertConnection A.key₀ (ident 0) []
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


-- One isolated installation; all following core records refer to this value.
installed : IG.Runtime
installed = Data.Product.proj₁ (fromMaybe (IG.initial , [])
  (IG.step Shared.responderMode (IG.installHandle (ident 0) (ident 0) A.key₀ [] duplex) IG.initial []))
installedInactive installedFlushed : IG.Runtime
installedInactive = record installed { continuation = IG.exitFlush; execution = record (IG.execution installed) { active = false } }
installedFlushed = record installedInactive { continuation = IG.exited }
info : Shared.NewConnectionInfo
info = Shared.newConnectionInfo inbound A.key₀ duplex (ident 0)
worldSuccess : Shared.AdmissionPC → Shared.ConnectionState → List Shared.IGEvent → Shared.State
worldSuccess pc st queue = Shared.state (Shared.cmStore (Shared.full binding) ((ident 0 , st) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ pc) ∷ []) ((A.child₀ , captured) ∷ [])
  ((ident 0 , Shared.handling A.child₀) ∷ []) (ident 0 ∷ []) 1
  ((ident 0 , Shared.negotiated (ident 0) duplex) ∷ []) queue []
connectedState : Shared.State
connectedState = worldSuccess (Shared.completedHandshake (Shared.connected info))
  (Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex) (Shared.newConnection info ∷ [])
cleanupLease : Shared.Lease
cleanupLease = Shared.lease A.child₀ binding
cleanWorld : Shared.MapCell → Shared.ConnectionState → Shared.SocketOwner → Shared.CleanupPC → List Shared.IGEvent → Shared.State
cleanWorld cell st sock pc queue = Shared.state (Shared.cmStore cell ((ident 0 , st) ∷ []) 1)
  ((A.w₀ , Shared.admissionWorker A.r₀ (Shared.completedHandshake (Shared.connected info))) ∷ [])
  ((A.child₀ , captured) ∷ []) ((ident 0 , sock) ∷ []) (ident 0 ∷ []) 1
  ((ident 0 , Shared.negotiated (ident 0) duplex) ∷ []) queue ((A.child₀ , pc) ∷ [])
cleaned : List Shared.IGEvent → Shared.State
cleaned = cleanWorld (Shared.full []) (Shared.terminated nothing) Shared.closed (Shared.cleanupCount Shared.cleanupNormal)
coreOf : Shared.State → IG.Runtime → Machine.Configuration
coreOf world ig = record c₀ { world = world; inboundGovernor = ig }

s0 : Outer
s0 = start

c1 : Machine.Configuration
c1 = coreOf w1 IG.initial

a1 : OuterAction
a1 = server (S.acceptedFork A.w₀ A.r₀)
s1 : Outer
s1 = render c1 (nothing) (nothing) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e1 : outerStep a1 s0 ≡ just s1
e1 = refl

-- Small component target; the full outer edge below checks success.
c2 : Machine.Configuration
c2 = coreOf w2 IG.initial

a2 : OuterAction
a2 = admit Admission.take
s2 : Outer
s2 = render c2 (nothing) (nothing) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e2 : outerStep a2 s1 ≡ just s2
e2 = refl

-- Small component target; the full outer edge below checks success.
c3 : Machine.Configuration
c3 = coreOf w3 IG.initial

a3 : OuterAction
a3 = admit Admission.countLimit
s3 : Outer
s3 = render c3 (nothing) (nothing) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e3 : outerStep a3 s2 ≡ just s3
e3 = refl

-- Small component target; the full outer edge below checks success.
c4 : Machine.Configuration
c4 = coreOf w4 IG.initial

a4 : OuterAction
a4 = admit Admission.allocatePromise
s4 : Outer
s4 = render c4 (nothing) (nothing) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e4 : outerStep a4 s3 ≡ just s4
e4 = refl

-- Small component target; the full outer edge below checks success.
c5 : Machine.Configuration
c5 = coreOf w5 IG.initial

a5 : OuterAction
a5 = admit Admission.chooseEntry
s5 : Outer
s5 = render c5 (nothing) (nothing) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e5 : outerStep a5 s4 ≡ just s5
e5 = refl

-- Small component target; the full outer edge below checks success.
c6 : Machine.Configuration
c6 = coreOf w6 IG.initial

a6 : OuterAction
a6 = admit Admission.fork
s6 : Outer
s6 = render c6 (just H.maskedSetup) (nothing) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e6 : outerStep a6 s5 ≡ just s6
e6 = refl

-- Small component target; the full outer edge below checks success.
c7 : Machine.Configuration
c7 = coreOf w7 IG.initial

a7 : OuterAction
a7 = admit Admission.putMapBack
s7 : Outer
s7 = render c7 (just H.maskedSetup) (nothing) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e7 : outerStep a7 s6 ≡ just s7
e7 = refl

-- Small component target; the full outer edge below checks success.
c8 : Machine.Configuration
c8 = coreOf w8 IG.initial

a8 : OuterAction
a8 = admit Admission.readCounters
s8 : Outer
s8 = render c8 (just H.maskedSetup) (nothing) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e8 : outerStep a8 s7 ≡ just s8
e8 = refl

a9 : OuterAction
a9 = handler (H.enterHandshake A.child₀)
s9 : Outer
s9 = render c8 (just H.handshaking) (nothing) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e9 : outerStep a9 s8 ≡ just s9
e9 = refl

a10 : OuterAction
a10 = runU (N.U.negotiate A.child₀ [] duplex)
s10 : Outer
s10 = render c8 (just H.handshaking) (just (frame N.U.returnedSuccess N.S.initial)) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e10 : outerStep a10 s9 ≡ just s10
e10 = refl

-- Small component target; the full outer edge below checks success.
c11 : Machine.Configuration
c11 = coreOf w8 installed

a11 : OuterAction
a11 = runU (N.U.allocateHandle A.child₀ (ident 0) (ident 0))
s11 : Outer
s11 = render c11 (just H.handshaking) (just (frame (N.U.handleAllocated (ident 0) (ident 0)) N.S.initial)) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e11 : outerStep a11 s10 ≡ just s11
e11 = refl

-- Small component target; the full outer edge below checks success.
c12 : Machine.Configuration
c12 = coreOf (worldSuccess (Shared.awaitHandshake (ident 0) (ident 0)) (Shared.unnegotiated inbound A.key₀ A.child₀) []) installed

a12 : OuterAction
a12 = runU (N.U.publishSuccess A.child₀)
s12 : Outer
s12 = render c12 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e12 : outerStep a12 s11 ≡ just s12
e12 = refl

-- Small component target; the full outer edge below checks success.
c13 : Machine.Configuration
c13 = coreOf (worldSuccess (Shared.commitHandshake (ident 0) (Shared.negotiated (ident 0) duplex)) (Shared.unnegotiated inbound A.key₀ A.child₀) []) installed

a13 : OuterAction
a13 = consume Handshake.readResult
s13 : Outer
s13 = render c13 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e13 : outerStep a13 s12 ≡ just s13
e13 = refl

-- Small component target; the full outer edge below checks success.
c14 : Machine.Configuration
c14 = coreOf (worldSuccess (Shared.countHandshake (Shared.connected info)) (Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex) []) installed

a14 : OuterAction
a14 = consume Handshake.commitResult
s14 : Outer
s14 = render c14 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e14 : outerStep a14 s13 ≡ just s14
e14 = refl

-- Small component target; the full outer edge below checks success.
c15 : Machine.Configuration
c15 = coreOf (worldSuccess (Shared.notifyInbound info) (Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex) []) installed

a15 : OuterAction
a15 = consume Handshake.readResultCounters
s15 : Outer
s15 = render c15 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e15 : outerStep a15 s14 ≡ just s15
e15 = refl

-- Small component target; the full outer edge below checks success.
c16 : Machine.Configuration
c16 = coreOf (worldSuccess (Shared.returnHandshake (Shared.connected info)) (Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex) (Shared.newConnection info ∷ [])) installed

a16 : OuterAction
a16 = consume Handshake.enqueueInbound
s16 : Outer
s16 = render c16 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e16 : outerStep a16 s15 ≡ just s16
e16 = refl

-- Small component target; the full outer edge below checks success.
c17 : Machine.Configuration
c17 = coreOf connectedState installed

a17 : OuterAction
a17 = consume Handshake.returnResult
s17 : Outer
s17 = render c17 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ S.calling 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e17 : outerStep a17 s16 ≡ just s17
e17 = refl

a18 : OuterAction
a18 = server (S.workerReturned A.w₀)
s18 : Outer
s18 = render c17 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ (S.bodyExited S.returned) 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e18 : outerStep a18 s17 ≡ just s18
e18 = refl

a19 : OuterAction
a19 = server (S.workerResult A.w₀)
s19 : Outer
s19 = render c17 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , false) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e19 : outerStep a19 s18 ≡ just s19
e19 = refl

a20 : OuterAction
a20 = innerAct (joinWorker A.w₀)
s20 : Outer
s20 = render c17 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (nothing) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e20 : outerStep a20 s19 ≡ just s20
e20 = refl

a21 : OuterAction
a21 = runR (N.R.observeFailure A.child₀ N.R.bufferAcquire err)
s21 : Outer
s21 = render c17 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.readyBody) (nothing)
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e21 : outerStep a21 s20 ≡ just s21
e21 = refl

a22 : OuterAction
a22 = runR (N.R.handoff A.child₀)
s22 : Outer
s22 = render c17 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.classifying err))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e22 : outerStep a22 s21 ≡ just s22
e22 = refl

a23 : OuterAction
a23 = runW (N.W.choosePolicy A.child₀ Life.shutdownPeer)
s23 : Outer
s23 = render c17 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.errorTracing err Life.shutdownPeer))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e23 : outerStep a23 s22 ≡ just s23
e23 = refl

a24 : OuterAction
a24 = runW (N.W.observeErrorTrace A.child₀)
s24 : Outer
s24 = render c17 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.peerRethrow err))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e24 : outerStep a24 s23 ≡ just s24
e24 = refl

a25 : OuterAction
a25 = runW (N.W.rethrow A.child₀)
s25 : Outer
s25 = render c17 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.bodyExited (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e25 : outerStep a25 s24 ≡ just s25
e25 = refl

-- Small component target; the full outer edge below checks success.
c26 : Machine.Configuration
c26 = coreOf (cleanWorld (Shared.full binding) (Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex) (Shared.handling A.child₀) Shared.cleanupAcquire (Shared.newConnection info ∷ [])) installed

a26 : OuterAction
a26 = runW (N.W.enterFinalizer A.child₀)
s26 : Outer
s26 = render c26 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e26 : outerStep a26 s25 ≡ just s26
e26 = refl

-- Small component target; the full outer edge below checks success.
c27 : Machine.Configuration
c27 = coreOf (cleanWorld (Shared.taken A.child₀) (Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex) (Shared.handling A.child₀) (Shared.cleanupSelect cleanupLease) (Shared.newConnection info ∷ [])) installed

a27 : OuterAction
a27 = runW (N.W.cleanup A.child₀ Cleanup.takeCleanupMap)
s27 : Outer
s27 = render c27 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e27 : outerStep a27 s26 ≡ just s27
e27 = refl

-- Small component target; the full outer edge below checks success.
c28 : Machine.Configuration
c28 = coreOf (cleanWorld (Shared.taken A.child₀) (Shared.terminated nothing) (Shared.handling A.child₀) (Shared.cleanupClose cleanupLease [] Shared.countImmediately) (Shared.newConnection info ∷ [])) installed

a28 : OuterAction
a28 = runW (N.W.cleanup A.child₀ Cleanup.selectCleanupEntry)
s28 : Outer
s28 = render c28 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e28 : outerStep a28 s27 ≡ just s28
e28 = refl

-- Small component target; the full outer edge below checks success.
c29 : Machine.Configuration
c29 = coreOf (cleanWorld (Shared.taken A.child₀) (Shared.terminated nothing) Shared.closed (Shared.cleanupPublish cleanupLease [] Shared.countImmediately) (Shared.newConnection info ∷ [])) installed

a29 : OuterAction
a29 = runW (N.W.cleanup A.child₀ Cleanup.closeHandlerSocket)
s29 : Outer
s29 = render c29 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e29 : outerStep a29 s28 ≡ just s29
e29 = refl

-- Small component target; the full outer edge below checks success.
c30 : Machine.Configuration
c30 = coreOf (cleaned (Shared.newConnection info ∷ [])) installed

a30 : OuterAction
a30 = runW (N.W.cleanup A.child₀ Cleanup.publishCleanupMap)
s30 : Outer
s30 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k₀ S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e30 : outerStep a30 s29 ≡ just s30
e30 = refl

k31 : C.Context
k31 = record k₀ { scopes = Scope.scopeState Scope.running Scope.running Scope.running Scope.running (Scope.closing Scope.churn) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a31 : OuterAction
a31 = scope Scope.beginUnwind
s31 : Outer
s31 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k31 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e31 : outerStep a31 s30 ≡ just s31
e31 = refl

k32 : C.Context
k32 = record k₀ { scopes = Scope.scopeState Scope.cancelRequested Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a32 : OuterAction
a32 = scope Scope.requestCancel
s32 : Outer
s32 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k32 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e32 : outerStep a32 s31 ≡ just s32
e32 = refl

k33 : C.Context
k33 = record k₀ { scopes = Scope.scopeState Scope.cancelDelivered Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a33 : OuterAction
a33 = scope Scope.deliverCancel
s33 : Outer
s33 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k33 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e33 : outerStep a33 s32 ≡ just s33
e33 = refl

k34 : C.Context
k34 = record k₀ { scopes = Scope.scopeState Scope.bodyExited Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a34 : OuterAction
a34 = scope (Scope.bodyExit Scope.churn)
s34 : Outer
s34 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k34 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e34 : outerStep a34 s33 ≡ just s34
e34 = refl

k35 : C.Context
k35 = record k₀ { scopes = Scope.scopeState Scope.resultAvailable Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a35 : OuterAction
a35 = scope (Scope.publishResult Scope.churn)
s35 : Outer
s35 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k35 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e35 : outerStep a35 s34 ≡ just s35
e35 = refl

k36 : C.Context
k36 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.running Scope.running Scope.running (Scope.closing Scope.governor) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a36 : OuterAction
a36 = scope Scope.join
s36 : Outer
s36 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k36 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e36 : outerStep a36 s35 ≡ just s36
e36 = refl

k37 : C.Context
k37 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.cancelRequested Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a37 : OuterAction
a37 = scope Scope.requestCancel
s37 : Outer
s37 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k37 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e37 : outerStep a37 s36 ≡ just s37
e37 = refl

k38 : C.Context
k38 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.cancelDelivered Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.openPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a38 : OuterAction
a38 = scope Scope.deliverCancel
s38 : Outer
s38 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k38 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e38 : outerStep a38 s37 ≡ just s38
e38 = refl

k39 : C.Context
k39 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.cancelDelivered Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closing }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a39 : OuterAction
a39 = peer (PS.run (PS.GP.beginClose []))
s39 : Outer
s39 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k39 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e39 : outerStep a39 s38 ≡ just s39
e39 = refl

k40 : C.Context
k40 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.cancelDelivered Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a40 : OuterAction
a40 = peer (PS.run PS.GP.finishClose)
s40 : Outer
s40 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k40 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e40 : outerStep a40 s39 ≡ just s40
e40 = refl

k41 : C.Context
k41 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.bodyExited Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a41 : OuterAction
a41 = scope (Scope.bodyExit Scope.governor)
s41 : Outer
s41 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k41 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e41 : outerStep a41 s40 ≡ just s41
e41 = refl

k42 : C.Context
k42 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.resultAvailable Scope.running Scope.running (Scope.closing Scope.governor) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a42 : OuterAction
a42 = scope (Scope.publishResult Scope.governor)
s42 : Outer
s42 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k42 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e42 : outerStep a42 s41 ≡ just s42
e42 = refl

k43 : C.Context
k43 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.running Scope.running (Scope.closing Scope.localRoot) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a43 : OuterAction
a43 = scope Scope.join
s43 : Outer
s43 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k43 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e43 : outerStep a43 s42 ≡ just s43
e43 = refl

k44 : C.Context
k44 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.cancelRequested Scope.running (Scope.closing Scope.localRoot) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a44 : OuterAction
a44 = scope Scope.requestCancel
s44 : Outer
s44 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k44 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e44 : outerStep a44 s43 ≡ just s44
e44 = refl

k45 : C.Context
k45 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.cancelDelivered Scope.running (Scope.closing Scope.localRoot) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a45 : OuterAction
a45 = scope Scope.deliverCancel
s45 : Outer
s45 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k45 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e45 : outerStep a45 s44 ≡ just s45
e45 = refl

k46 : C.Context
k46 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.bodyExited Scope.running (Scope.closing Scope.localRoot) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a46 : OuterAction
a46 = scope (Scope.bodyExit Scope.localRoot)
s46 : Outer
s46 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k46 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e46 : outerStep a46 s45 ≡ just s46
e46 = refl

k47 : C.Context
k47 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.resultAvailable Scope.running (Scope.closing Scope.localRoot) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a47 : OuterAction
a47 = scope (Scope.publishResult Scope.localRoot)
s47 : Outer
s47 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k47 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e47 : outerStep a47 s46 ≡ just s47
e47 = refl

k48 : C.Context
k48 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.running (Scope.closing Scope.ledger) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a48 : OuterAction
a48 = scope Scope.join
s48 : Outer
s48 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k48 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e48 : outerStep a48 s47 ≡ just s48
e48 = refl

k49 : C.Context
k49 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.cancelRequested (Scope.closing Scope.ledger) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a49 : OuterAction
a49 = scope Scope.requestCancel
s49 : Outer
s49 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k49 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e49 : outerStep a49 s48 ≡ just s49
e49 = refl

k50 : C.Context
k50 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.cancelDelivered (Scope.closing Scope.ledger) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a50 : OuterAction
a50 = scope Scope.deliverCancel
s50 : Outer
s50 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k50 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e50 : outerStep a50 s49 ≡ just s50
e50 = refl

k51 : C.Context
k51 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.bodyExited (Scope.closing Scope.ledger) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a51 : OuterAction
a51 = scope (Scope.bodyExit Scope.ledger)
s51 : Outer
s51 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k51 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e51 : outerStep a51 s50 ≡ just s51
e51 = refl

k52 : C.Context
k52 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.resultAvailable (Scope.closing Scope.ledger) true
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a52 : OuterAction
a52 = scope (Scope.publishResult Scope.ledger)
s52 : Outer
s52 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k52 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e52 : outerStep a52 s51 ≡ just s52
e52 = refl

k53 : C.Context
k53 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.readyToFinish) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a53 : OuterAction
a53 = scope Scope.join
s53 : Outer
s53 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k53 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e53 : outerStep a53 s52 ≡ just s53
e53 = refl

k54 : C.Context
k54 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.openPool } }

a54 : OuterAction
a54 = scope Scope.finishClose
s54 : Outer
s54 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k54 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e54 : outerStep a54 s53 ≡ just s54
e54 = refl

k55 : C.Context
k55 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closing } }

a55 : OuterAction
a55 = peer (PS.beginMonitorClose [])
s55 : Outer
s55 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k55 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e55 : outerStep a55 s54 ≡ just s55
e55 = refl

k56 : C.Context
k56 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a56 : OuterAction
a56 = peer PS.finishMonitorClose
s56 : Outer
s56 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k56 S.serving true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e56 : outerStep a56 s55 ≡ just s56
e56 = refl

k57 : C.Context
k57 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a57 : OuterAction
a57 = server (S.scope S.returnAction)
s57 : Outer
s57 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k57 S.actionBodyExited true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e57 : outerStep a57 s56 ≡ just s57
e57 = refl

k58 : C.Context
k58 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a58 : OuterAction
a58 = server (S.scope S.publishActionResult)
s58 : Outer
s58 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k58 S.actionResultAvailable true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e58 : outerStep a58 s57 ≡ just s58
e58 = refl

k59 : C.Context
k59 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a59 : OuterAction
a59 = server (S.scope S.selectActionWinner)
s59 : Outer
s59 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k59 S.closingAccept true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e59 : outerStep a59 s58 ≡ just s59
e59 = refl

k60 : C.Context
k60 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a60 : OuterAction
a60 = server (S.scope S.requestAcceptCancel)
s60 : Outer
s60 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k60 S.acceptCancelRequested true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e60 : outerStep a60 s59 ≡ just s60
e60 = refl

k61 : C.Context
k61 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a61 : OuterAction
a61 = server (S.scope S.deliverAcceptAtWait)
s61 : Outer
s61 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k61 S.acceptCancelDelivered true S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e61 : outerStep a61 s60 ≡ just s61
e61 = refl

k62 : C.Context
k62 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a62 : OuterAction
a62 = server (S.scope S.closeListener)
s62 : Outer
s62 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k62 S.acceptBodyExited false S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e62 : outerStep a62 s61 ≡ just s62
e62 = refl

k63 : C.Context
k63 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a63 : OuterAction
a63 = server (S.scope S.publishAcceptResult)
s63 : Outer
s63 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k63 S.acceptResultAvailable false S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e63 : outerStep a63 s62 ≡ just s63
e63 = refl

k64 : C.Context
k64 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a64 : OuterAction
a64 = server (S.scope S.joinAccept)
s64 : Outer
s64 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k64 S.acceptJoined false S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e64 : outerStep a64 s63 ≡ just s64
e64 = refl

k65 : C.Context
k65 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a65 : OuterAction
a65 = server (S.scope S.traceStopped)
s65 : Outer
s65 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k65 S.serverStopped false S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e65 : outerStep a65 s64 ≡ just s65
e65 = refl

k66 : C.Context
k66 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a66 : OuterAction
a66 = server (S.scope S.cancelJoinReturnedAction)
s66 : Outer
s66 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k66 S.actionJoined false S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e66 : outerStep a66 s65 ≡ just s66
e66 = refl

k67 : C.Context
k67 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a67 : OuterAction
a67 = server (S.scope S.requestIGCancel)
s67 : Outer
s67 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k67 S.igCancelRequested false S.igLive E.emptyExit (Close.initialState) (RR.initial true)
e67 : outerStep a67 s66 ≡ just s67
e67 = refl

k68 : C.Context
k68 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a68 : OuterAction
a68 = exit (E.receive E.loopBoundary err)
s68 : Outer
s68 = render c30 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k68 S.igCancelRequested false S.igCaught caught (Close.initialState) (RR.initial true)
e68 : outerStep a68 s67 ≡ just s68
e68 = refl

-- Small component target; the full outer edge below checks success.
c69 : Machine.Configuration
c69 = coreOf (cleaned (Shared.newConnection info ∷ [])) installedInactive

k69 : C.Context
k69 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a69 : OuterAction
a69 = server (S.scope S.deactivateIG)
s69 : Outer
s69 = render c69 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k69 S.igCancelRequested false S.igInactive caught (Close.initialState) (RR.initial true)
e69 : outerStep a69 s68 ≡ just s69
e69 = refl

-- Small component target; the full outer edge below checks success.
c70 : Machine.Configuration
c70 = coreOf (cleaned []) installedFlushed

k70 : C.Context
k70 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a70 : OuterAction
a70 = server (S.scope S.flushIG)
s70 : Outer
s70 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k70 S.igCancelRequested false S.igFlushed caught (Close.initialState) (RR.initial true)
e70 : outerStep a70 s69 ≡ just s70
e70 = refl

k71 : C.Context
k71 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a71 : OuterAction
a71 = exit E.captureSnapshot
s71 : Outer
s71 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k71 S.igCancelRequested false S.igFlushed traversing (Close.initialState) (RR.initial true)
e71 : outerStep a71 s70 ≡ just s71
e71 = refl

k72 : C.Context
k72 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a72 : OuterAction
a72 = exit E.finishFinal
s72 : Outer
s72 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k72 S.igCancelRequested false S.igBodyExited bodyDone (Close.initialState) (RR.initial true)
e72 : outerStep a72 s71 ≡ just s72
e72 = refl

k73 : C.Context
k73 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a73 : OuterAction
a73 = server (S.scope S.publishIGResult)
s73 : Outer
s73 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k73 S.igCancelRequested false S.igResultAvailable resultDone (Close.initialState) (RR.initial true)
e73 : outerStep a73 s72 ≡ just s73
e73 = refl

k74 : C.Context
k74 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a74 : OuterAction
a74 = server (S.scope S.joinIG)
s74 : Outer
s74 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k74 S.igJoined false S.igResultAvailable resultDone (Close.initialState) (RR.initial true)
e74 : outerStep a74 s73 ≡ just s74
e74 = refl

k75 : C.Context
k75 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a75 : OuterAction
a75 = server (S.scope S.beginCM)
s75 : Outer
s75 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k75 S.closingCM false S.igResultAvailable resultDone (Close.initialState) (RR.initial true)
e75 : outerStep a75 s74 ≡ just s75
e75 = refl

k76 : C.Context
k76 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a76 : OuterAction
a76 = coordinator Close.captureSnapshot
s76 : Outer
s76 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k76 S.closingCM false S.igResultAvailable resultDone (Close.shutdownState Close.reading [] [] []) (RR.initial true)
e76 : outerStep a76 s75 ≡ just s76
e76 = refl

k77 : C.Context
k77 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a77 : OuterAction
a77 = coordinator Close.finishTraversal
s77 : Outer
s77 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k77 S.closingCM false S.igResultAvailable resultDone (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
e77 : outerStep a77 s76 ≡ just s77
e77 = refl

k78 : C.Context
k78 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a78 : OuterAction
a78 = coordinator Close.finishClose
s78 : Outer
s78 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k78 S.closingCM false S.igResultAvailable resultDone (Close.shutdownState Close.closed [] [] []) (RR.initial true)
e78 : outerStep a78 s77 ≡ just s78
e78 = refl

k79 : C.Context
k79 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a79 : OuterAction
a79 = server (S.scope S.finishServer)
s79 : Outer
s79 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k79 S.serverReturned false S.igResultAvailable resultDone (Close.shutdownState Close.closed [] [] []) (RR.initial true)
e79 : outerStep a79 s78 ≡ just s79
e79 = refl

k80 : C.Context
k80 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a80 : OuterAction
a80 = relaysAct RR.requestCancel
s80 : Outer
s80 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k80 S.serverReturned false S.igResultAvailable resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.cancelRequested) RR.cancelling)
e80 : outerStep a80 s79 ≡ just s80
e80 = refl

k81 : C.Context
k81 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a81 : OuterAction
a81 = relaysAct (RR.threadAct RR.deliverCancel)
s81 : Outer
s81 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k81 S.serverReturned false S.igResultAvailable resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.cancelDelivered) RR.cancelling)
e81 : outerStep a81 s80 ≡ just s81
e81 = refl

k82 : C.Context
k82 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a82 : OuterAction
a82 = relaysAct (RR.threadAct RR.bodyExit)
s82 : Outer
s82 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k82 S.serverReturned false S.igResultAvailable resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.bodyExited) RR.cancelling)
e82 : outerStep a82 s81 ≡ just s82
e82 = refl

k83 : C.Context
k83 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a83 : OuterAction
a83 = relaysAct (RR.threadAct RR.publishResult)
s83 : Outer
s83 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k83 S.serverReturned false S.igResultAvailable resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.resultAvailable) RR.cancelling)
e83 : outerStep a83 s82 ≡ just s83
e83 = refl

k84 : C.Context
k84 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a84 : OuterAction
a84 = relaysAct (RR.threadAct RR.join)
s84 : Outer
s84 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k84 S.serverReturned false S.igResultAvailable resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.joined) RR.cancelling)
e84 : outerStep a84 s83 ≡ just s84
e84 = refl

k85 : C.Context
k85 = record k₀ { scopes = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false
  ; governorPool = record PS.GP.Pool.initial { phase = PS.GP.Pool.closedPool }
  ; monitorPool = record PS.Pool.initial { phase = PS.Pool.closedPool } }

a85 : OuterAction
a85 = relaysAct RR.finish
s85 : Outer
s85 = render c70 (just H.handshaking) (just (frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException err)))
  ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) k85 S.serverReturned false S.igResultAvailable resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.joined) RR.finished)
e85 : outerStep a85 s84 ≡ just s85
e85 = refl

actions : List OuterAction
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ a19 ∷ a20 ∷ a21 ∷ a22 ∷ a23 ∷ a24 ∷ a25 ∷ a26 ∷ a27 ∷ a28 ∷ a29 ∷ a30 ∷ a31 ∷ a32 ∷ a33 ∷ a34 ∷ a35 ∷ a36 ∷ a37 ∷ a38 ∷ a39 ∷ a40 ∷ a41 ∷ a42 ∷ a43 ∷ a44 ∷ a45 ∷ a46 ∷ a47 ∷ a48 ∷ a49 ∷ a50 ∷ a51 ∷ a52 ∷ a53 ∷ a54 ∷ a55 ∷ a56 ∷ a57 ∷ a58 ∷ a59 ∷ a60 ∷ a61 ∷ a62 ∷ a63 ∷ a64 ∷ a65 ∷ a66 ∷ a67 ∷ a68 ∷ a69 ∷ a70 ∷ a71 ∷ a72 ∷ a73 ∷ a74 ∷ a75 ∷ a76 ∷ a77 ∷ a78 ∷ a79 ∷ a80 ∷ a81 ∷ a82 ∷ a83 ∷ a84 ∷ a85 ∷ []
abstract
  counterexample-run : Executes start actions s85
  counterexample-run = next e1 (next e2 (next e3 (next e4 (next e5 (next e6 (next e7 (next e8 (next e9 (next e10 (next e11 (next e12 (next e13 (next e14 (next e15 (next e16 (next e17 (next e18 (next e19 (next e20 (next e21 (next e22 (next e23 (next e24 (next e25 (next e26 (next e27 (next e28 (next e29 (next e30 (next e31 (next e32 (next e33 (next e34 (next e35 (next e36 (next e37 (next e38 (next e39 (next e40 (next e41 (next e42 (next e43 (next e44 (next e45 (next e46 (next e47 (next e48 (next e49 (next e50 (next e51 (next e52 (next e53 (next e54 (next e55 (next e56 (next e57 (next e58 (next e59 (next e60 (next e61 (next e62 (next e63 (next e64 (next e65 (next e66 (next e67 (next e68 (next e69 (next e70 (next e71 (next e72 (next e73 (next e74 (next e75 (next e76 (next e77 (next e78 (next e79 (next e80 (next e81 (next e82 (next e83 (next e84 (next e85 (done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
-- Read the same physical registry/oracle used by the real CM wrapper.
serverOf : Outer → S.State
serverOf s = E.base (K.server (T.base (source (inner s))))
physical : Outer → N.W.State
physical s = N.R.base (N.raw (S.base (serverOf s)))
coord : Outer → Close.State
coord s = N.W.shutdown (physical s)


-- The success result has been consumed and the raw worker joined BEFORE purge.
connected-worker : lookup A.w₀ (Shared.admissions (S.shared (serverOf s20))) ≡
  just (Shared.admissionWorker A.r₀ (Shared.completedHandshake
    (Shared.connected (Shared.newConnectionInfo inbound A.key₀ duplex (ident 0)))))
connected-worker = refl
worker-joined : lookup A.w₀ (owned (inner s20)) ≡ just true
worker-joined = refl
self-purged : Shared.mapCell (Shared.cm (S.shared (serverOf s30))) ≡ Shared.full []
self-purged = refl
paused-at-counters : lookup A.child₀ (Shared.cleanups (S.shared (serverOf s85))) ≡
  just (Shared.cleanupCount Shared.cleanupNormal)
paused-at-counters = refl
finished-relays : RR.owner (relays s85) ≡ RR.finished
finished-relays = refl
closed-empty : coord s85 ≡ Close.shutdownState Close.closed [] [] []
closed-empty = refl
unavailable : N.W.resultReady A.child₀ (physical s85) ≡ false
unavailable = refl
live-handler : lookup A.child₀ (B.threads (N.W.physical (physical s85))) ≡
  just (H.handlerThread captured H.handshaking)
live-handler = refl
open import Data.List.Membership.Propositional using (_∈_)
LiveCovered : Outer → Set
LiveCovered s = ∀ w h → lookup w (B.threads (N.W.physical (physical s))) ≡ just h →
  N.W.resultReady w (physical s) ≡ false → w ∈ Close.collected (coord s)
not-quiescent : LiveCovered s85 → ⊥
not-quiescent covered = case covered A.child₀ _ live-handler unavailable of λ ()
-- Erasure includes the explicit successful handshake/finalizer source schedule.
source-run : SourceOuter.Executes (eraseOuter start) (eraseActions actions) (eraseOuter s85)
source-run = outer-erasure counterexample-run
