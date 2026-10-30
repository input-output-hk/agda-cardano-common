{-# OPTIONS --guardedness #-}

-- Actual inbound birth followed by CM-owned blocking-tracer receipt/cleanup.
-- Retained caller PCs are logical captures; this partial model does not certify
-- a live caller job after CM scope exit or its outer cancellation lifetime.
module ConnectionManagement.Negative.MuxPublicationInboundCM where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
import ConnectionManagement.Negative.MuxPublicationInbound as B
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.MuxPublicationUnwind as Proof
import ConnectionManagement.Negative.MuxStartupUnwindFixtures as Fixture
import ConnectionManagement.Scenarios.Admission as Admission
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Store as Store
import ConnectionManagement.Properties.PromiseWait as PromiseWait
private
  module N = Publication I.bearerClosed
  module C = N.C
  module D = N.D
  module R = N.R
  module X = D.X
  module W = N.W
  module Facts = Proof I.bearerClosed
  module F = Fixture I.bearerClosed I.owner I.captured (ident 0)
  module S = B.Scenario B.newMuxAsync
owner : WorkerId
owner = I.owner
withShutdown : Close.State → N.State → N.State
withShutdown pc s = record s { base = record (N.base s) { base = record (C.base (N.base s))
  { base = F.withShutdown pc (N.raw s) } } }
reading wait : Close.State
reading = Close.shutdownState Close.reading (ident 0 ∷ []) [] (owner ∷ [])
wait = Close.shutdownState Close.awaitResults (ident 0 ∷ []) [] (owner ∷ [])
q0 q1 q2 q3 q4 q5 : N.State
q0 = S.s0
q1 = withShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) q0
q2 = withShutdown (Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []) q0
q3 = withShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) q0
q4 = withShutdown reading S.s1
q5 = withShutdown wait S.s2
edge1 : N.step (B.runR (R.run (X.run (W.shutdownStep Close.captureSnapshot)))) q0 ≡ just q1
edge1 = refl
edge2 : N.step (B.runR (R.run (X.run (W.shutdownStep Close.readEntry)))) q1 ≡ just q2
edge2 = refl
edge3 : N.step (B.runR (R.run (X.run (W.shutdownStep Close.requestCancellation)))) q2 ≡ just q3
edge3 = refl
edge4 : N.step (N.deliverShutdown N.newMuxTracer B.err) q3 ≡ just q4
edge4 = refl
edge5 : N.step (B.runR (R.run (X.run (W.shutdownStep Close.finishTraversal)))) q4 ≡ just q5
edge5 = refl
qActions : List N.Action
qActions = B.runR (R.run (X.run (W.shutdownStep Close.captureSnapshot))) ∷
  B.runR (R.run (X.run (W.shutdownStep Close.readEntry))) ∷
  B.runR (R.run (X.run (W.shutdownStep Close.requestCancellation))) ∷
  N.deliverShutdown N.newMuxTracer B.err ∷ B.runR (R.run (X.run (W.shutdownStep Close.finishTraversal))) ∷ []
qPath : N.Executes q0 qActions q5
qPath = N.next edge1 (N.next edge2 (N.next edge3 (N.next edge4 (N.next edge5 N.done))))
v3 : N.State
v3 = withShutdown wait S.s3
edge-v3 : N.step (B.runR (R.run (X.run (W.enterFinalizer owner)))) q5 ≡ just v3
edge-v3 = refl
v4 : N.State
v4 = withShutdown wait S.s4
edge-v4 : N.step (B.runR (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) v3 ≡ just v4
edge-v4 = refl
v5 : N.State
v5 = withShutdown wait S.s5
edge-v5 : N.step (B.runR (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) v4 ≡ just v5
edge-v5 = refl
v6 : N.State
v6 = withShutdown wait S.s6
edge-v6 : N.step (B.runR (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) v5 ≡ just v6
edge-v6 = refl
v7 : N.State
v7 = withShutdown wait S.s7
edge-v7 : N.step (B.runR (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) v6 ≡ just v7
edge-v7 = refl
v8 : N.State
v8 = withShutdown wait S.s8
edge-v8 : N.step (B.runR (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) v7 ≡ just v8
edge-v8 = refl
v9 : N.State
v9 = withShutdown wait S.s9
edge-v9 : N.step (B.runR (R.run (X.run (W.finishCleanup owner)))) v8 ≡ just v9
edge-v9 = refl
v10 : N.State
v10 = withShutdown wait S.s10
edge-v10 : N.step (B.runR (R.run (X.run (W.publishAsyncResult owner)))) v9 ≡ just v10
edge-v10 = refl
vActions : List N.Action
vActions = (B.runR (R.run (X.run (W.enterFinalizer owner)))) ∷ (B.runR (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) ∷ (B.runR (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) ∷ (B.runR (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) ∷ (B.runR (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) ∷ (B.runR (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) ∷ (B.runR (R.run (X.run (W.finishCleanup owner)))) ∷ (B.runR (R.run (X.run (W.publishAsyncResult owner)))) ∷ []
vPath : N.Executes q5 vActions v10
vPath = N.next edge-v3 (N.next edge-v4 (N.next edge-v5 (N.next edge-v6 (N.next edge-v7 (N.next edge-v8 (N.next edge-v9 (N.next edge-v10 (N.done))))))))
-- Admission executed its real counter read before negotiation. The captured
-- caller is already at awaitHandshake; no post-close API step is inserted.
waitingResult : N.State
waitingResult = v10
closed : N.State
closed = withShutdown (Close.shutdownState Close.closed (ident 0 ∷ []) [] (owner ∷ [])) waitingResult
final-close : N.step (B.runR (R.run (X.run (W.shutdownStep Close.finishClose)))) waitingResult ≡ just closed
final-close = refl
allActions : List N.Action
allActions = B.headActions B.newMuxAsync ++ (qActions ++ (vActions ++
  (B.runR (R.run (X.run (W.shutdownStep Close.finishClose))) ∷ [])))
abstract
  initialized : N.Executes B.initial allActions closed
  initialized = Facts.append (B.headPrefix B.newMuxAsync)
    (Facts.append qPath (Facts.append vPath (N.next final-close N.done)))
wait-before-cleanup : N.step (B.runR (R.run (X.run (W.shutdownStep Close.finishClose)))) q5 ≡ nothing
wait-before-cleanup = refl
wait-after-cleanup : N.step (B.runR (R.run (X.run (W.shutdownStep Close.finishClose)))) v9 ≡ nothing
wait-after-cleanup = refl
physical-wait : Facts.Exit.PhysicalWait (R.base (N.raw waitingResult)) (R.base (N.raw closed))
physical-wait = Facts.physical-wait waitingResult final-close
promise-is-not-physical-result : Store.lookup (ident 0) (Shared.handshakeResults (Machine.world (O.core (N.source closed)))) ≡ nothing
promise-is-not-physical-result = refl
physical-result : W.resultReady owner (R.base (N.raw closed)) ≡ true
physical-result = refl
caller-at-promise-wait : Store.lookup Admission.w₀
  (Shared.admissions (Machine.world (O.core (N.source closed)))) ≡
  just (Shared.admissionWorker Admission.r₀ (Shared.awaitHandshake (ident 0) (ident 0)))
caller-at-promise-wait = refl
raw-source-read-blocked : Machine.advance
  (Machine.handshakeStep Admission.w₀ Handshake.readResult) (O.core (N.source closed)) ≡ nothing
raw-source-read-blocked = PromiseWait.inbound-read-retries (O.core (N.source closed))
  Admission.w₀ Admission.r₀ (ident 0) (ident 0) caller-at-promise-wait promise-is-not-physical-result
map-purged : Shared.mapCell (Shared.cm (Machine.world (O.core (N.source closed)))) ≡ Shared.full []
map-purged = refl
socket-closed : Store.lookup (ident 0) (Shared.sockets (Machine.world (O.core (N.source closed)))) ≡ just Shared.closed
socket-closed = refl
