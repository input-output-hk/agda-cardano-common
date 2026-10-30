{-# OPTIONS --guardedness #-}

-- CM cancellation at a blocking pre-publication TraceNewMux. Promise reading
-- and physical Async-result waiting remain distinct after actual cleanup.
module ConnectionManagement.Negative.MuxPublicationUnwindCM where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
import ConnectionManagement.Negative.MuxPublicationUnwind as B
import ConnectionManagement.Negative.MuxPublicationFixtures as Old
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Store as Store
import ConnectionManagement.Properties.PromiseWait as PromiseWait
module N = B.N
module C = B.C
module D = B.D
module R = B.R
module X = B.X
module W = B.W
module Facts = B.Facts
module F = B.F
module S = B.Scenario B.newMuxAsync
import ConnectionManagement.OutboundHandlerSupervision as Outbound
import ConnectionManagement.Rules.OutboundAcquire as Acquire
owner : WorkerId
owner = Old.owner
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
-- Advance the caller while the CM coordinator is still awaiting results.
-- No successful API operation is inserted after the CM scope has closed.
waitingResult : N.State
waitingResult = B.readyCaller v10
counter-read : N.step (B.runP (N.P.run (N.U.run (Outbound.outbound (O.acquire Old.Fixture.caller Acquire.readCounters))))) v10 ≡ just waitingResult
counter-read = refl
closed : N.State
closed = withShutdown (Close.shutdownState Close.closed (ident 0 ∷ []) [] (owner ∷ [])) waitingResult
final-close : N.step (B.runR (R.run (X.run (W.shutdownStep Close.finishClose)))) waitingResult ≡ just closed
final-close = refl
allActions : List N.Action
allActions = B.headActions B.newMuxAsync ++ (qActions ++ (vActions ++
  (B.runP (N.P.run (N.U.run (Outbound.outbound (O.acquire Old.Fixture.caller Acquire.readCounters)))) ∷
   B.runR (R.run (X.run (W.shutdownStep Close.finishClose))) ∷ [])))
abstract
  initialized : N.Executes B.initial allActions closed
  initialized = Facts.append (B.headPrefix B.newMuxAsync)
    (Facts.append qPath (Facts.append vPath (N.next counter-read (N.next final-close N.done))))
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
caller-at-promise-wait : Store.lookup Old.Fixture.caller (O.acquiring (N.source closed)) ≡ just (Acquire.frame Old.Fixture.req Old.Fixture.wait)
caller-at-promise-wait = refl
-- Collective CM completion observes Async results, not handshake promises.
caller-read-after-CM-close : N.step (B.runP (N.P.run (N.U.run (Outbound.outbound (O.acquire Old.Fixture.caller Acquire.readResult))))) closed ≡ nothing
caller-read-after-CM-close = refl
raw-source-read-blocked : O.advance (O.acquire Old.Fixture.caller Acquire.readResult) (N.source closed) ≡ nothing
raw-source-read-blocked = PromiseWait.outbound-read-retries (N.source closed)
  Old.Fixture.caller Old.Fixture.req (ident 0) (ident 0) (Shared.handlerKey Old.Prior.captured)
  caller-at-promise-wait promise-is-not-physical-result

-- Apply the same source-level bridge to all five initialized pre-publication failure histories.
-- Matching the real PC rules out a refusal at the earlier counter-reading PC.
raw-source-for-every-case : ∀ which →
  O.advance (O.acquire Old.Fixture.caller Acquire.readResult) (N.source (B.state11 which)) ≡ nothing
raw-source-for-every-case which = PromiseWait.outbound-read-retries (N.source (B.state11 which))
  Old.Fixture.caller Old.Fixture.req (ident 0) (ident 0) (Shared.handlerKey Old.Prior.captured)
  (B.Scenario.caller-at-promise-wait which) (B.case-promise-remains-empty which)
physical-result-at-every-wait : ∀ which →
  W.resultOf owner (R.base (N.raw (B.state11 which))) ≡ just (B.body which)
physical-result-at-every-wait which = B.Scenario.parent-result which
