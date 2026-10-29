{-# OPTIONS --guardedness #-}

-- Actual CM snapshot/read/send, observed initiator-trace receipt, physical result
-- wait. Provider/tracer inputs remain explicit; no global shutdown is inferred.
module ConnectionManagement.Negative.MuxInitiatorTraceCM where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
import ConnectionManagement.Negative.MuxDeltaQ as Base
import ConnectionManagement.Negative.MuxInitiatorTraceEffects as E
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Properties.MuxHandlerExit as ExitProof
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxResultMonitor as RF
module D = E.D
module Facts = E.Facts
module Prefix = E.Prefix
module R = E.R
module X = E.X
module W = E.W
module G = E.G
module M = E.M
module P = E.P
module Pool = E.Pool
module F = E.F
module ExitFacts = ExitProof RF.bearerClosed
owner : WorkerId
owner = Old.owner
withShutdown : Close.State → D.State → D.State
withShutdown pc s = record s { base = F.withShutdown pc (D.base s) }
reading wait : Close.State
reading = Close.shutdownState Close.reading (ident 0 ∷ []) [] (owner ∷ [])
wait = Close.shutdownState Close.awaitResults (ident 0 ∷ []) [] (owner ∷ [])
-- Case analysis is confined to the real callback observation, not a forged
-- normal return. The two origins carry Ready and Failed(original), respectively.
receipt : ∀ origin → D.step (D.deliverInitiatorShutdown E.err)
  (withShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) (E.ready origin)) ≡ just
  (withShutdown reading (E.selected origin (R.async E.err) R.awaitingClose (E.mux origin) (E.queue origin) E.K.k0))
receipt E.cleanCompletion = refl
receipt E.errorCompletion = refl

module Scenario (origin : E.Origin) where
  module C = E.Close origin (R.async E.err)
  module A = E.Async origin
  q0 q1 q2 q3 q4 q5 : D.State
  q0 = E.ready origin
  q1 = withShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) q0
  q2 = withShutdown (Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []) q0
  q3 = withShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) q0
  q4 = withShutdown reading C.f1
  q5 = withShutdown wait C.f1
  q-edge1 : D.step (D.run (R.run (X.run (W.shutdownStep Close.captureSnapshot)))) q0 ≡ just q1
  q-edge1 = refl
  q-edge2 : D.step (D.run (R.run (X.run (W.shutdownStep Close.readEntry)))) q1 ≡ just q2
  q-edge2 = refl
  q-edge3 : D.step (D.run (R.run (X.run (W.shutdownStep Close.requestCancellation)))) q2 ≡ just q3
  q-edge3 = refl
  q-edge4 : D.step (D.deliverInitiatorShutdown E.err) q3 ≡ just q4
  q-edge4 = receipt origin
  q-edge5 : D.step (D.run (R.run (X.run (W.shutdownStep Close.finishTraversal)))) q4 ≡ just q5
  q-edge5 = refl
  qActions : List D.Action
  qActions = D.run (R.run (X.run (W.shutdownStep Close.captureSnapshot))) ∷ D.run (R.run (X.run (W.shutdownStep Close.readEntry))) ∷
    D.run (R.run (X.run (W.shutdownStep Close.requestCancellation))) ∷ D.deliverInitiatorShutdown E.err ∷
    D.run (R.run (X.run (W.shutdownStep Close.finishTraversal))) ∷ []
  qPath : D.Executes q0 qActions q5
  qPath = D.next q-edge1 (D.next q-edge2 (D.next q-edge3 (D.next q-edge4 (D.next q-edge5 D.done))))
  receipt-is-not-join : Pool.phase (D.poolAt owner q4) ≡ Pool.openPool
  receipt-is-not-join = refl
  receipt-is-not-parent-result : W.resultReady owner (R.base (D.base q4)) ≡ false
  receipt-is-not-parent-result = refl
  wait-before-pool-close : D.step (D.run (R.run (X.run (W.shutdownStep Close.finishClose)))) q5 ≡ nothing
  wait-before-pool-close = refl
  child0 : D.State
  child0 = withShutdown wait C.c0
  child-edge0 : D.step (D.run (R.beginClose owner E.K.order)) q5 ≡ just child0
  child-edge0 = refl
  child1 : D.State
  child1 = withShutdown wait C.c1
  child-edge1 : D.step (D.run (R.requestCancel owner)) child0 ≡ just child1
  child-edge1 = refl
  child2 : D.State
  child2 = withShutdown wait C.c2
  child-edge2 : D.step (D.run (R.deliverCancel owner)) child1 ≡ just child2
  child-edge2 = refl
  child3 : D.State
  child3 = withShutdown wait C.c3
  child-edge3 : D.step (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₁₀))))) child2 ≡ just child3
  child-edge3 = refl
  child4 : D.State
  child4 = withShutdown wait C.c4
  child-edge4 : D.step (Base.runM (M.run (P.deregisterProtocol Old.j₁₀))) child3 ≡ just child4
  child-edge4 = refl
  child5 : D.State
  child5 = withShutdown wait C.c5
  child-edge5 : D.step (Base.runM (M.run (P.asyncProtocolResult Old.j₁₀))) child4 ≡ just child5
  child-edge5 = refl
  u2 : D.State
  u2 = withShutdown wait C.f2
  child-edge6 : D.step (D.run (R.join owner)) child5 ≡ just u2
  child-edge6 = refl
  u3 : D.State
  u3 = withShutdown wait C.f3
  u-edge3 : D.step (D.run (R.requestCancel owner)) u2 ≡ just u3
  u-edge3 = refl
  u4 : D.State
  u4 = withShutdown wait C.f4
  u-edge4 : D.step (D.run (R.deliverCancel owner)) u3 ≡ just u4
  u-edge4 = refl
  u5 : D.State
  u5 = withShutdown wait C.f5
  u-edge5 : D.step (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₁))))) u4 ≡ just u5
  u-edge5 = refl
  u6 : D.State
  u6 = withShutdown wait C.f6
  u-edge6 : D.step (Base.runM (M.run (P.deregisterInfra owner T.demuxer))) u5 ≡ just u6
  u-edge6 = refl
  u7 : D.State
  u7 = withShutdown wait C.f7
  u-edge7 : D.step (Base.runM (M.run (P.asyncInfraResult owner T.demuxer))) u6 ≡ just u7
  u-edge7 = refl
  u8 : D.State
  u8 = withShutdown wait C.f8
  u-edge8 : D.step (D.run (R.join owner)) u7 ≡ just u8
  u-edge8 = refl
  u9 : D.State
  u9 = withShutdown wait C.f9
  u-edge9 : D.step (D.run (R.requestCancel owner)) u8 ≡ just u9
  u-edge9 = refl
  u10 : D.State
  u10 = withShutdown wait C.f10
  u-edge10 : D.step (D.run (R.deliverCancel owner)) u9 ≡ just u10
  u-edge10 = refl
  u11 : D.State
  u11 = withShutdown wait C.f11
  u-edge11 : D.step (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₀))))) u10 ≡ just u11
  u-edge11 = refl
  u12 : D.State
  u12 = withShutdown wait C.f12
  u-edge12 : D.step (Base.runM (M.run (P.deregisterInfra owner T.muxer))) u11 ≡ just u12
  u-edge12 = refl
  u13 : D.State
  u13 = withShutdown wait C.f13
  u-edge13 : D.step (Base.runM (M.run (P.asyncInfraResult owner T.muxer))) u12 ≡ just u13
  u-edge13 = refl
  u14 : D.State
  u14 = withShutdown wait C.f14
  u-edge14 : D.step (D.run (R.join owner)) u13 ≡ just u14
  u-edge14 = refl
  u15 : D.State
  u15 = withShutdown wait C.f15
  u-edge15 : D.step (D.run (R.finishClose owner)) u14 ≡ just u15
  u-edge15 = refl
  uActions : List D.Action
  uActions = (D.run (R.beginClose owner E.K.order)) ∷ (D.run (R.requestCancel owner)) ∷ (D.run (R.deliverCancel owner)) ∷ (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₁₀))))) ∷ (Base.runM (M.run (P.deregisterProtocol Old.j₁₀))) ∷ (Base.runM (M.run (P.asyncProtocolResult Old.j₁₀))) ∷ (D.run (R.join owner)) ∷ (D.run (R.requestCancel owner)) ∷ (D.run (R.deliverCancel owner)) ∷ (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₁))))) ∷ (Base.runM (M.run (P.deregisterInfra owner T.demuxer))) ∷ (Base.runM (M.run (P.asyncInfraResult owner T.demuxer))) ∷ (D.run (R.join owner)) ∷ (D.run (R.requestCancel owner)) ∷ (D.run (R.deliverCancel owner)) ∷ (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₀))))) ∷ (Base.runM (M.run (P.deregisterInfra owner T.muxer))) ∷ (Base.runM (M.run (P.asyncInfraResult owner T.muxer))) ∷ (D.run (R.join owner)) ∷ (D.run (R.finishClose owner)) ∷ []
  uPath : D.Executes q5 uActions u15
  uPath = D.next child-edge0 (D.next child-edge1 (D.next child-edge2 (D.next child-edge3 (D.next child-edge4 (D.next child-edge5 (D.next child-edge6 (D.next u-edge3 (D.next u-edge4 (D.next u-edge5 (D.next u-edge6 (D.next u-edge7 (D.next u-edge8 (D.next u-edge9 (D.next u-edge10 (D.next u-edge11 (D.next u-edge12 (D.next u-edge13 (D.next u-edge14 (D.next u-edge15 (D.done))))))))))))))))))))
  v16 : D.State
  v16 = withShutdown wait A.a16
  v-edge16 : D.step (D.run (R.writeAsyncFailure owner)) u15 ≡ just v16
  v-edge16 = refl
  v17 : D.State
  v17 = withShutdown wait A.a17
  v-edge17 : D.step (D.run (R.beginDead owner)) v16 ≡ just v17
  v-edge17 = refl
  v18 : D.State
  v18 = withShutdown wait A.a18
  v-edge18 : D.step (D.run (R.sampleDead owner)) v17 ≡ just v18
  v-edge18 = refl
  v19 : D.State
  v19 = withShutdown wait A.a19
  v-edge19 : D.step (D.run (R.commitDead owner)) v18 ≡ just v19
  v-edge19 = refl
  v20 : D.State
  v20 = withShutdown wait A.a20
  v-edge20 : D.step (D.run (R.finishDead owner)) v19 ≡ just v20
  v-edge20 = refl
  v21 : D.State
  v21 = withShutdown wait A.a21
  v-edge21 : D.step (D.run (R.handoff owner)) v20 ≡ just v21
  v-edge21 = refl
  v22 : D.State
  v22 = withShutdown wait A.a22
  v-edge22 : D.step (D.run (R.run (X.run (W.observeBufferReturn owner)))) v21 ≡ just v22
  v-edge22 = refl
  v23 : D.State
  v23 = withShutdown wait A.a23
  v-edge23 : D.step (D.run (R.run (X.run (W.enterFinalizer owner)))) v22 ≡ just v23
  v-edge23 = refl
  v24 : D.State
  v24 = withShutdown wait A.a24
  v-edge24 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) v23 ≡ just v24
  v-edge24 = refl
  v25 : D.State
  v25 = withShutdown wait A.a25
  v-edge25 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) v24 ≡ just v25
  v-edge25 = refl
  v26 : D.State
  v26 = withShutdown wait A.a26
  v-edge26 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) v25 ≡ just v26
  v-edge26 = refl
  v27 : D.State
  v27 = withShutdown wait A.a27
  v-edge27 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) v26 ≡ just v27
  v-edge27 = refl
  v28 : D.State
  v28 = withShutdown wait A.a28
  v-edge28 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) v27 ≡ just v28
  v-edge28 = refl
  v29 : D.State
  v29 = withShutdown wait A.a29
  v-edge29 : D.step (D.run (R.run (X.run (W.finishCleanup owner)))) v28 ≡ just v29
  v-edge29 = refl
  v30 : D.State
  v30 = withShutdown wait A.a30
  v-edge30 : D.step (D.run (R.run (X.run (W.publishAsyncResult owner)))) v29 ≡ just v30
  v-edge30 = refl
  vActions : List D.Action
  vActions = (D.run (R.writeAsyncFailure owner)) ∷ (D.run (R.beginDead owner)) ∷ (D.run (R.sampleDead owner)) ∷ (D.run (R.commitDead owner)) ∷ (D.run (R.finishDead owner)) ∷ (D.run (R.handoff owner)) ∷ (D.run (R.run (X.run (W.observeBufferReturn owner)))) ∷ (D.run (R.run (X.run (W.enterFinalizer owner)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) ∷ (D.run (R.run (X.run (W.finishCleanup owner)))) ∷ (D.run (R.run (X.run (W.publishAsyncResult owner)))) ∷ []
  vPath : D.Executes u15 vActions v30
  vPath = D.next v-edge16 (D.next v-edge17 (D.next v-edge18 (D.next v-edge19 (D.next v-edge20 (D.next v-edge21 (D.next v-edge22 (D.next v-edge23 (D.next v-edge24 (D.next v-edge25 (D.next v-edge26 (D.next v-edge27 (D.next v-edge28 (D.next v-edge29 (D.next v-edge30 (D.done)))))))))))))))
  closed : D.State
  closed = withShutdown (Close.shutdownState Close.closed (ident 0 ∷ []) [] (owner ∷ [])) v30
  final-close : D.step (D.run (R.run (X.run (W.shutdownStep Close.finishClose)))) v30 ≡ just closed
  final-close = refl
  allActions : List D.Action
  allActions = E.readyActions origin ++ (qActions ++ (uActions ++ (vActions ++
    (D.run (R.run (X.run (W.shutdownStep Close.finishClose))) ∷ []))))
  abstract
    initialized : D.Executes Base.start allActions closed
    initialized = Prefix.append (E.initialized-ready origin)
      (Prefix.append qPath (Prefix.append uPath (Prefix.append vPath (D.next final-close D.done))))
  physical-wait : ExitFacts.PhysicalWait (R.base (D.base v30)) (R.base (D.base closed))
  physical-wait = Facts.physical-wait v30 final-close
  no-result-at-buffer-exit : W.resultReady owner (R.base (D.base v22)) ≡ false
  no-result-at-buffer-exit = refl
  no-result-at-cleanup-end : W.resultReady owner (R.base (D.base v29)) ≡ false
  no-result-at-cleanup-end = refl
  wait-after-cleanup-before-result : D.step (D.run (R.run (X.run (W.shutdownStep Close.finishClose)))) v29 ≡ nothing
  wait-after-cleanup-before-result = refl
  actual-parent-result : W.resultReady owner (R.base (D.base v30)) ≡ true
  actual-parent-result = refl
  captures : Capture.Captures (D.source closed)
  captures = Facts.from-initial-captures Base.actual-initializer initialized
  supply : Supply.Valid (D.source closed)
  supply = Facts.from-initial-supply Base.actual-initializer Old.Prior.initial-bounds initialized
  source-and-pool-paths : Facts.Paths Base.start closed
  source-and-pool-paths = Facts.exec-projects initialized

  -- The bearer callback has not been invoked at this cancellation site.
  no-DeltaQ-substitution : D.step (D.deliverShutdown E.err) q3 ≡ nothing
  no-DeltaQ-substitution = refl
  wait-after-pool-close : D.step (D.run (R.run (X.run (W.shutdownStep Close.finishClose)))) u15 ≡ nothing
  wait-after-pool-close = refl

module Clean = Scenario E.cleanCompletion
module Error = Scenario E.errorCompletion
