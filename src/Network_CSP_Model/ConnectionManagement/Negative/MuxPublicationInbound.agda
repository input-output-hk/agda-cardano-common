{-# OPTIONS --guardedness #-}

-- Actual initialized inbound births, pre-publication faults, original
-- cleanup and a raw promise retry at the certified awaitHandshake continuation.
module ConnectionManagement.Negative.MuxPublicationInbound where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Properties.PromiseWait as PromiseWait
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.MuxPublicationUnwind as Proof
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.MuxStartupUnwindFixtures as Fixture
import ConnectionManagement.Negative.MuxHandlerExitFixtures as CleanupFixtures
import ConnectionManagement.CSP.Fixtures as Src
import ConnectionManagement.Scenarios.Admission as Admission
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.CMShutdown as Close
private
  module N = Publication I.bearerClosed
  module Facts = Proof I.bearerClosed
  module C = N.C
  module D = N.D
  module R = N.R
  module X = D.X
  module W = N.W
  module G = N.G
  module P = N.P
  module U = N.U
  module M = N.M
  module S = N.S
  module Pool = N.Pool
  module F = Fixture I.bearerClosed I.owner I.captured (ident 0)
  module Clean = CleanupFixtures I.bearerClosed I.owner I.captured
owner : WorkerId
owner = I.owner
err : ErrorId
err = errorId 92
delta : P.State → D.State
delta p = D.deltaQState (R.unwinding (W.handlerExitState
  (G.shutdownState (M.monitorState p []) []) []) []) []
wrap : P.State → N.State
wrap p = N.publicationState (C.catchState (delta p) []) []
runP : P.Action → N.Action
runP action = N.run (C.run (D.run (D.wrapMonitor (M.run action))))
runR : R.Action → N.Action
runR action = N.run (C.run (D.run action))
initial : N.State
initial = wrap I.p0
actual-initializer : N.initial (O.initial Src.start) ≡ just initial
actual-initializer = refl
prefix1 : N.step (runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.take)))))) (wrap I.p0) ≡ just (wrap I.p1)
prefix1 = refl
prefix2 : N.step (runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.countLimit)))))) (wrap I.p1) ≡ just (wrap I.p2)
prefix2 = refl
prefix3 : N.step (runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.allocatePromise)))))) (wrap I.p2) ≡ just (wrap I.p3)
prefix3 = refl
prefix4 : N.step (runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.chooseEntry)))))) (wrap I.p3) ≡ just (wrap I.p4)
prefix4 = refl
prefix5 : N.step (runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.fork)))))) (wrap I.p4) ≡ just (wrap I.p5)
prefix5 = refl
prefix6 : N.step (runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.putMapBack)))))) (wrap I.p5) ≡ just (wrap I.p6)
prefix6 = refl
prefix7 : N.step (runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.readCounters)))))) (wrap I.p6) ≡ just (wrap I.p7)
prefix7 = refl
prefix8 : N.step (runP (P.run (U.run (B.handler (H.enterHandshake owner))))) (wrap I.p7) ≡ just (wrap I.p8)
prefix8 = refl
prefix9 : N.step (runP (P.run (U.negotiate owner I.ps duplex))) (wrap I.p8) ≡ just (wrap I.p9)
prefix9 = refl
beforeActions : List N.Action
beforeActions = runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.take))))) ∷ runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.countLimit))))) ∷ runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.allocatePromise))))) ∷ runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.chooseEntry))))) ∷ runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.fork))))) ∷ runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.putMapBack))))) ∷ runP (P.run (U.run (B.handler (H.run (Machine.admissionStep Admission.w₀ Server.readCounters))))) ∷ runP (P.run (U.run (B.handler (H.enterHandshake owner)))) ∷ runP (P.run (U.negotiate owner I.ps duplex)) ∷ []
abstract
  beforePrefix : N.Executes initial beforeActions (wrap I.p9)
  beforePrefix = N.next prefix1 (N.next prefix2 (N.next prefix3 (N.next prefix4 (N.next prefix5 (N.next prefix6 (N.next prefix7 (N.next prefix8 (N.next prefix9 (N.done)))))))))
data Case : Set where
  successSync successAsync newMuxSync newMuxAsync allocationSync : Case
site : Case → N.Site
site successSync = N.handshakeSuccessTracer
site successAsync = N.handshakeSuccessTracer
site newMuxSync = N.newMuxTracer
site allocationSync = N.muxAllocation
site newMuxAsync = N.newMuxTracer
exception : Case → R.Exception
exception successSync = R.sync err
exception successAsync = R.async err
exception newMuxSync = R.sync err
exception allocationSync = R.sync err
exception newMuxAsync = R.async err
body : Case → W.BodyResult
body successSync = W.peerException err
body successAsync = W.asyncException err
body newMuxSync = W.peerException err
body allocationSync = W.peerException err
body newMuxAsync = W.asyncException err
head : Case → P.State
head successSync = I.p9
head successAsync = I.p9
head newMuxSync = I.p9
head allocationSync = I.p9
head newMuxAsync = I.p9
frame : Case → U.Frame
frame successSync = I.successFrame
frame successAsync = I.successFrame
frame newMuxSync = I.successFrame
frame allocationSync = I.successFrame
frame newMuxAsync = I.successFrame
at : Case → W.Phase → N.State
at which phase = N.publicationState
  (C.catchState (record (delta (head which))
    { base = F.withExit phase (D.base (delta (head which))) }) [])
  ((owner , N.failure (frame which) (site which) (exception which)) ∷ [])
cleaned : Case → W.Phase → Shared.State → N.State
cleaned which phase world = record (at which phase) { base = record (N.base (at which phase))
  { base = record (C.base (N.base (at which phase))) { base = F.withWorld world (N.raw (at which phase)) } } }
headActions : Case → List N.Action
headActions successSync = beforeActions
headActions successAsync = beforeActions
headActions newMuxSync = beforeActions
headActions allocationSync = beforeActions
headActions newMuxAsync = beforeActions
headPrefix : ∀ which → N.Executes initial (headActions which) (wrap (head which))
headPrefix successSync = beforePrefix
headPrefix successAsync = beforePrefix
headPrefix newMuxSync = beforePrefix
headPrefix allocationSync = beforePrefix
headPrefix newMuxAsync = beforePrefix
observe : ∀ which → N.step (N.observeFailure owner (site which) (exception which)) (wrap (head which)) ≡ just (at which (N.target (exception which)))
observe successSync = refl
observe successAsync = refl
observe newMuxSync = refl
observe allocationSync = refl
observe newMuxAsync = refl
policyActions : List N.Action
policyActions = runR (R.run (X.run (W.choosePolicy owner Life.shutdownPeer))) ∷
  runR (R.run (X.run (W.observeErrorTrace owner))) ∷ runR (R.run (X.run (W.rethrow owner))) ∷ []
policy : Case → List N.Action
policy successAsync = []
policy newMuxAsync = []
policy _ = policyActions
policy1 : ∀ which → N.step (runR (R.run (X.run (W.choosePolicy owner Life.shutdownPeer)))) (at which (W.classifying err)) ≡ just (at which (W.errorTracing err Life.shutdownPeer))
policy1 which = refl
policy2 : ∀ which → N.step (runR (R.run (X.run (W.observeErrorTrace owner)))) (at which (W.errorTracing err Life.shutdownPeer)) ≡ just (at which (W.peerRethrow err))
policy2 which = refl
policy3 : ∀ which → N.step (runR (R.run (X.run (W.rethrow owner)))) (at which (W.peerRethrow err)) ≡ just (at which (W.bodyExited (W.peerException err)))
policy3 which = refl
policyPath : ∀ which → N.Executes (at which (N.target (exception which))) (policy which) (at which (W.bodyExited (body which)))
policyPath successAsync = N.done
policyPath newMuxAsync = N.done
policyPath successSync = N.next (policy1 successSync) (N.next (policy2 successSync) (N.next (policy3 successSync) N.done))
policyPath newMuxSync = N.next (policy1 newMuxSync) (N.next (policy2 newMuxSync) (N.next (policy3 newMuxSync) N.done))
policyPath allocationSync = N.next (policy1 allocationSync) (N.next (policy2 allocationSync) (N.next (policy3 allocationSync) N.done))

state0 : Case → N.State
state0 which = wrap (head which)
state1 : Case → N.State
state1 which = at which (N.target (exception which))
state2 : Case → N.State
state2 which = at which (W.bodyExited (body which))
state3 : Case → N.State
state3 which = cleaned which (W.finalizing (body which)) (Clean.world1 (Machine.world (O.core (P.source (head which)))))
state4 : Case → N.State
state4 which = cleaned which (W.finalizing (body which)) (Clean.world2 (Machine.world (O.core (P.source (head which)))))
state5 : Case → N.State
state5 which = cleaned which (W.finalizing (body which)) (Clean.world3 (Machine.world (O.core (P.source (head which)))))
state6 : Case → N.State
state6 which = cleaned which (W.finalizing (body which)) (Clean.world4 (Machine.world (O.core (P.source (head which)))))
state7 : Case → N.State
state7 which = cleaned which (W.finalizing (body which)) (Clean.world5 (Machine.world (O.core (P.source (head which)))))
state8 : Case → N.State
state8 which = cleaned which (W.finalizing (body which)) (Clean.world6 (Machine.world (O.core (P.source (head which)))))
state9 : Case → N.State
state9 which = cleaned which (W.cleanupComplete (body which) Shared.cleanupNormal) (Clean.world6 (Machine.world (O.core (P.source (head which)))))
state10 : Case → N.State
state10 which = cleaned which (W.resultAvailable (body which) Shared.cleanupNormal) (Clean.world6 (Machine.world (O.core (P.source (head which)))))
advance3 : ∀ which → N.step (runR (R.run (X.run (W.enterFinalizer owner)))) (state2 which) ≡ just (state3 which)
advance3 successSync = refl
advance3 successAsync = refl
advance3 newMuxSync = refl
advance3 allocationSync = refl
advance3 newMuxAsync = refl
advance4 : ∀ which → N.step (runR (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) (state3 which) ≡ just (state4 which)
advance4 successSync = refl
advance4 successAsync = refl
advance4 newMuxSync = refl
advance4 allocationSync = refl
advance4 newMuxAsync = refl
advance5 : ∀ which → N.step (runR (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) (state4 which) ≡ just (state5 which)
advance5 successSync = refl
advance5 successAsync = refl
advance5 newMuxSync = refl
advance5 allocationSync = refl
advance5 newMuxAsync = refl
advance6 : ∀ which → N.step (runR (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) (state5 which) ≡ just (state6 which)
advance6 successSync = refl
advance6 successAsync = refl
advance6 newMuxSync = refl
advance6 allocationSync = refl
advance6 newMuxAsync = refl
advance7 : ∀ which → N.step (runR (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) (state6 which) ≡ just (state7 which)
advance7 successSync = refl
advance7 successAsync = refl
advance7 newMuxSync = refl
advance7 allocationSync = refl
advance7 newMuxAsync = refl
advance8 : ∀ which → N.step (runR (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) (state7 which) ≡ just (state8 which)
advance8 successSync = refl
advance8 successAsync = refl
advance8 newMuxSync = refl
advance8 allocationSync = refl
advance8 newMuxAsync = refl
advance9 : ∀ which → N.step (runR (R.run (X.run (W.finishCleanup owner)))) (state8 which) ≡ just (state9 which)
advance9 successSync = refl
advance9 successAsync = refl
advance9 newMuxSync = refl
advance9 allocationSync = refl
advance9 newMuxAsync = refl
advance10 : ∀ which → N.step (runR (R.run (X.run (W.publishAsyncResult owner)))) (state9 which) ≡ just (state10 which)
advance10 successSync = refl
advance10 successAsync = refl
advance10 newMuxSync = refl
advance10 allocationSync = refl
advance10 newMuxAsync = refl
case-promise-remains-empty : ∀ which → lookup (ident 0) (Shared.handshakeResults (Machine.world (O.core (N.source (state10 which))))) ≡ nothing
case-promise-remains-empty successSync = refl
case-promise-remains-empty successAsync = refl
case-promise-remains-empty newMuxSync = refl
case-promise-remains-empty allocationSync = refl
case-promise-remains-empty newMuxAsync = refl
case-no-pool-adopted : ∀ which → N.poolAt owner (state10 which) ≡ Pool.initial
case-no-pool-adopted successSync = refl
case-no-pool-adopted successAsync = refl
case-no-pool-adopted newMuxSync = refl
case-no-pool-adopted allocationSync = refl
case-no-pool-adopted newMuxAsync = refl
-- Specialize observations before reducing the full concrete source record.
case-caller-at-promise-wait : ∀ which →
  lookup Admission.w₀ (Shared.admissions (Machine.world (O.core (N.source (state10 which))))) ≡
    just (Shared.admissionWorker Admission.r₀ (Shared.awaitHandshake (ident 0) (ident 0)))
case-caller-at-promise-wait successSync = refl
case-caller-at-promise-wait successAsync = refl
case-caller-at-promise-wait newMuxSync = refl
case-caller-at-promise-wait allocationSync = refl
case-caller-at-promise-wait newMuxAsync = refl
case-map-purged : ∀ which →
  Shared.mapCell (Shared.cm (Machine.world (O.core (N.source (state10 which))))) ≡ Shared.full []
case-map-purged successSync = refl
case-map-purged successAsync = refl
case-map-purged newMuxSync = refl
case-map-purged allocationSync = refl
case-map-purged newMuxAsync = refl
case-socket-closed : ∀ which →
  lookup (ident 0) (Shared.sockets (Machine.world (O.core (N.source (state10 which))))) ≡ just Shared.closed
case-socket-closed successSync = refl
case-socket-closed successAsync = refl
case-socket-closed newMuxSync = refl
case-socket-closed allocationSync = refl
case-socket-closed newMuxAsync = refl

module Scenario (which : Case) where
  originalWorld : Shared.State
  originalWorld = Machine.world (O.core (P.source (head which)))
  s0 : N.State
  s0 = state0 which
  s1 : N.State
  s1 = state1 which
  s2 : N.State
  s2 = state2 which
  s3 : N.State
  s3 = state3 which
  edge3 : N.step (runR (R.run (X.run (W.enterFinalizer owner)))) s2 ≡ just s3
  edge3 = advance3 which
  s4 : N.State
  s4 = state4 which
  edge4 : N.step (runR (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) s3 ≡ just s4
  edge4 = advance4 which
  s5 : N.State
  s5 = state5 which
  edge5 : N.step (runR (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) s4 ≡ just s5
  edge5 = advance5 which
  s6 : N.State
  s6 = state6 which
  edge6 : N.step (runR (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) s5 ≡ just s6
  edge6 = advance6 which
  s7 : N.State
  s7 = state7 which
  edge7 : N.step (runR (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) s6 ≡ just s7
  edge7 = advance7 which
  s8 : N.State
  s8 = state8 which
  edge8 : N.step (runR (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) s7 ≡ just s8
  edge8 = advance8 which
  s9 : N.State
  s9 = state9 which
  edge9 : N.step (runR (R.run (X.run (W.finishCleanup owner)))) s8 ≡ just s9
  edge9 = advance9 which
  s10 : N.State
  s10 = state10 which
  edge10 : N.step (runR (R.run (X.run (W.publishAsyncResult owner)))) s9 ≡ just s10
  edge10 = advance10 which
  cleanupActions : List N.Action
  cleanupActions = (runR (R.run (X.run (W.enterFinalizer owner)))) ∷ (runR (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) ∷ (runR (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) ∷ (runR (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) ∷ (runR (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) ∷ (runR (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) ∷ (runR (R.run (X.run (W.finishCleanup owner)))) ∷ (runR (R.run (X.run (W.publishAsyncResult owner)))) ∷ []
  cleanupPath : N.Executes s2 cleanupActions s10
  cleanupPath = N.next edge3 (N.next edge4 (N.next edge5 (N.next edge6 (N.next edge7 (N.next edge8 (N.next edge9 (N.next edge10 (N.done))))))))
  actions : List N.Action
  actions = headActions which ++ (N.observeFailure owner (site which) (exception which) ∷ (policy which ++ cleanupActions))
  abstract
    initialized : N.Executes initial actions s10
    initialized = Facts.append (headPrefix which)
      (N.next (observe which) (Facts.append (policyPath which) cleanupPath))
  promise-remains-empty : lookup (ident 0) (Shared.handshakeResults (Machine.world (O.core (N.source s10)))) ≡ nothing
  promise-remains-empty = case-promise-remains-empty which
  parent-result : W.resultOf owner (R.base (N.raw s10)) ≡ just (body which)
  parent-result = refl
  physical-result : W.resultReady owner (R.base (N.raw s10)) ≡ true
  physical-result = refl
  captured-unpublished-frame-retained : lookup owner (N.failures s10) ≡ just (N.failure (frame which) (site which) (exception which))
  captured-unpublished-frame-retained = refl
  no-pool-adopted : N.poolAt owner s10 ≡ Pool.initial
  no-pool-adopted = case-no-pool-adopted which
  no-late-publication : N.step (runP (P.run (U.publishSuccess owner))) s1 ≡ nothing
  no-late-publication = refl
  no-late-allocation : N.step (runP (P.run (U.allocateHandle owner (ident 1) (ident 1)))) s1 ≡ nothing
  no-late-allocation = refl
  caller-at-promise-wait : lookup Admission.w₀ (Shared.admissions (Machine.world (O.core (N.source s10)))) ≡
    just (Shared.admissionWorker Admission.r₀ (Shared.awaitHandshake (ident 0) (ident 0)))
  caller-at-promise-wait = case-caller-at-promise-wait which
  raw-source-read-blocked : Machine.advance
    (Machine.handshakeStep Admission.w₀ Handshake.readResult) (O.core (N.source s10)) ≡ nothing
  raw-source-read-blocked = PromiseWait.inbound-read-retries (O.core (N.source s10))
    Admission.w₀ Admission.r₀ (ident 0) (ident 0) caller-at-promise-wait promise-remains-empty
  map-purged : Shared.mapCell (Shared.cm (Machine.world (O.core (N.source s10)))) ≡ Shared.full []
  map-purged = case-map-purged which
  socket-closed : lookup (ident 0) (Shared.sockets (Machine.world (O.core (N.source s10)))) ≡ just Shared.closed
  socket-closed = case-socket-closed which
  captures : Capture.Captures (N.source s10)
  captures = Facts.from-initial-captures actual-initializer initialized
  supply : Supply.Valid (N.source s10)
  supply = Facts.from-initial-supply actual-initializer (All.[] , All.[]) initialized

module SuccessSync = Scenario successSync
module SuccessAsync = Scenario successAsync
module NewMuxSync = Scenario newMuxSync
module AllocationSync = Scenario allocationSync
module NewMuxAsync = Scenario newMuxAsync
