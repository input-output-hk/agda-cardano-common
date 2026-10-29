{-# OPTIONS --guardedness #-}

-- CM cancellation delivered at the blocking tracer in a post-close async catch.
-- Acknowledgment does not substitute for outer finally or physical completion.
module ConnectionManagement.Negative.MuxCatchUnwindCM where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
import ConnectionManagement.Negative.MuxCatchUnwind as B
import ConnectionManagement.Negative.MuxInitiatorTraceEffects as E
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Properties.MuxHandlerExit as ExitProof
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
module C = B.C
module D = B.D
module R = B.R
module X = B.X
module W = B.W
module Facts = B.Facts
module F = B.F
import ConnectionManagement.Negative.MuxResultMonitor as RF
module ExitFacts = ExitProof RF.bearerClosed
owner : WorkerId
owner = Old.owner
withShutdown : Close.State → C.State → C.State
withShutdown pc s = record s { base = record (C.base s) { base = F.withShutdown pc (D.base (C.base s)) } }
reading wait : Close.State
reading = Close.shutdownState Close.reading (ident 0 ∷ []) [] (owner ∷ [])
wait = Close.shutdownState Close.awaitResults (ident 0 ∷ []) [] (owner ∷ [])

module Scenario (origin : E.Origin) where
  module S = B.Scenario origin
  q0 q1 q2 q3 q4 q5 : C.State
  q0 = S.s0
  q1 = withShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) q0
  q2 = withShutdown (Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []) q0
  q3 = withShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) q0
  q4 = withShutdown reading S.s1
  q5 = withShutdown wait S.s1
  edge1 : C.step (C.run (D.run (R.run (X.run (W.shutdownStep Close.captureSnapshot))))) q0 ≡ just q1
  edge1 = refl
  edge2 : C.step (C.run (D.run (R.run (X.run (W.shutdownStep Close.readEntry))))) q1 ≡ just q2
  edge2 = refl
  edge3 : C.step (C.run (D.run (R.run (X.run (W.shutdownStep Close.requestCancellation))))) q2 ≡ just q3
  edge3 = refl
  edge4 : C.step (C.deliverShutdown C.blockedCallerTracer B.err) q3 ≡ just q4
  edge4 = refl
  edge5 : C.step (C.run (D.run (R.run (X.run (W.shutdownStep Close.finishTraversal))))) q4 ≡ just q5
  edge5 = refl
  qActions : List C.Action
  qActions = C.run (D.run (R.run (X.run (W.shutdownStep Close.captureSnapshot)))) ∷
    C.run (D.run (R.run (X.run (W.shutdownStep Close.readEntry)))) ∷
    C.run (D.run (R.run (X.run (W.shutdownStep Close.requestCancellation)))) ∷
    C.deliverShutdown C.blockedCallerTracer B.err ∷
    C.run (D.run (R.run (X.run (W.shutdownStep Close.finishTraversal)))) ∷ []
  qPath : C.Executes q0 qActions q5
  qPath = C.next edge1 (C.next edge2 (C.next edge3 (C.next edge4 (C.next edge5 C.done))))
  v2 : C.State
  v2 = withShutdown wait S.s2
  edge-v2 : C.step (C.run (D.run (R.handoff owner))) q5 ≡ just v2
  edge-v2 = refl
  v3 : C.State
  v3 = withShutdown wait S.s3
  edge-v3 : C.step (C.run (D.run (R.run (X.run (W.observeBufferReturn owner))))) v2 ≡ just v3
  edge-v3 = refl
  v4 : C.State
  v4 = withShutdown wait S.s4
  edge-v4 : C.step (C.run (D.run (R.run (X.run (W.enterFinalizer owner))))) v3 ≡ just v4
  edge-v4 = refl
  v5 : C.State
  v5 = withShutdown wait S.s5
  edge-v5 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap))))) v4 ≡ just v5
  edge-v5 = refl
  v6 : C.State
  v6 = withShutdown wait S.s6
  edge-v6 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry))))) v5 ≡ just v6
  edge-v6 = refl
  v7 : C.State
  v7 = withShutdown wait S.s7
  edge-v7 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket))))) v6 ≡ just v7
  edge-v7 = refl
  v8 : C.State
  v8 = withShutdown wait S.s8
  edge-v8 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap))))) v7 ≡ just v8
  edge-v8 = refl
  v9 : C.State
  v9 = withShutdown wait S.s9
  edge-v9 : C.step (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters))))) v8 ≡ just v9
  edge-v9 = refl
  v10 : C.State
  v10 = withShutdown wait S.s10
  edge-v10 : C.step (C.run (D.run (R.run (X.run (W.finishCleanup owner))))) v9 ≡ just v10
  edge-v10 = refl
  v11 : C.State
  v11 = withShutdown wait S.s11
  edge-v11 : C.step (C.run (D.run (R.run (X.run (W.publishAsyncResult owner))))) v10 ≡ just v11
  edge-v11 = refl
  vActions : List C.Action
  vActions = (C.run (D.run (R.handoff owner))) ∷ (C.run (D.run (R.run (X.run (W.observeBufferReturn owner))))) ∷ (C.run (D.run (R.run (X.run (W.enterFinalizer owner))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap))))) ∷ (C.run (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters))))) ∷ (C.run (D.run (R.run (X.run (W.finishCleanup owner))))) ∷ (C.run (D.run (R.run (X.run (W.publishAsyncResult owner))))) ∷ []
  vPath : C.Executes q5 vActions v11
  vPath = C.next edge-v2 (C.next edge-v3 (C.next edge-v4 (C.next edge-v5 (C.next edge-v6 (C.next edge-v7 (C.next edge-v8 (C.next edge-v9 (C.next edge-v10 (C.next edge-v11 (C.done))))))))))
  closed : C.State
  closed = withShutdown (Close.shutdownState Close.closed (ident 0 ∷ []) [] (owner ∷ [])) v11
  final-close : C.step (C.run (D.run (R.run (X.run (W.shutdownStep Close.finishClose))))) v11 ≡ just closed
  final-close = refl
  allActions : List C.Action
  allActions = map C.run (B.originalActions origin) ++ (qActions ++ (vActions ++
    (C.run (D.run (R.run (X.run (W.shutdownStep Close.finishClose)))) ∷ [])))
  abstract
    initialized : C.Executes B.initial allActions closed
    initialized = Facts.append S.prefix (Facts.append qPath (Facts.append vPath (C.next final-close C.done)))
  wait-after-receipt : C.step (C.run (D.run (R.run (X.run (W.shutdownStep Close.finishClose))))) q5 ≡ nothing
  wait-after-receipt = refl
  wait-after-cleanup : C.step (C.run (D.run (R.run (X.run (W.shutdownStep Close.finishClose))))) v10 ≡ nothing
  wait-after-cleanup = refl
  physical-wait : ExitFacts.PhysicalWait (R.base (D.base (C.base v11))) (R.base (D.base (C.base closed)))
  physical-wait = Facts.physical-wait v11 final-close
  replacement-result : W.resultOf owner (R.base (D.base (C.base closed))) ≡ just (W.asyncException B.err)
  replacement-result = refl
  captures : Capture.Captures (C.source closed)
  captures = Facts.from-initial-captures B.actual-initializer initialized
  supply : Supply.Valid (C.source closed)
  supply = Facts.from-initial-supply B.actual-initializer Old.Prior.initial-bounds initialized

module CleanOrigin = Scenario E.cleanCompletion
module ErrorOrigin = Scenario E.errorCompletion
