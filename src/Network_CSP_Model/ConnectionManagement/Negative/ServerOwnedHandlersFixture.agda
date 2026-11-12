{-# OPTIONS --guardedness #-}

-- Initialized progress and refusals for registry + phase B + OwnedCallers.
-- Each ordinary edge uses the actual selected source transition by computation.
module ConnectionManagement.Negative.ServerOwnedHandlersFixture where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerOwnedWorkersSelfPurge as F
import ConnectionManagement.Negative.ServerOwnedWorkersCounterexample as C
import ConnectionManagement.Negative.ServerAdmission as Late
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Variants.ServerOwnedHandlers as Variant
import ConnectionManagement.Properties.ServerOwnedHandlers as Facts
open Variant I.bearerClosed C.classify using (module N; module B; module S; module E; module K; unread; scanning; sending; waited)
open Variant.Protocols I.bearerClosed C.classify C.capability
open Facts.Protocols I.bearerClosed C.classify C.capability using (Quiescent; quiescence; si5; registry-si5)

-- Reuse the checked phase B source states, with the new registry metadata.
embed : W.Outer → Variant.Sweep I.bearerClosed C.classify → Outer
embed (W.outer b r) pc = outer (pack b [] pc) r
label : W.OuterAction → OuterAction
label (W.innerAct a) = innerAct (sourceEvent a)
label (W.relaysAct a) = relaysAct a

-- Original late admission is still refused at beginCM, even before the sweep.
module Ctx = Context C.classify
late-beginCM-refused : ∀ e (k : Ctx.Context) →
  advance (sourceEvent (W.run (T.dispatch (K.serverStep (E.run (S.scope S.beginCM))))))
    (pack (W.runtime (T.runtime (K.combined (E.igExitState (Late.atAfterIG S.igJoined) e) k) T.empty)
      ((A.w₀ , false) ∷ (A.w₁ , false) ∷ [])) [] unread) ≡ nothing
late-beginCM-refused e k = refl

-- The combined policy explicitly excludes the audited foreign begin route.
foreign-acquire-refused : ∀ s w req → advanceSource (W.run (T.dispatch (K.coreStep
  (ConnectionManagement.OutboundMachine.beginAcquire w req)))) s ≡ nothing
foreign-acquire-refused s w req with T.inheritAllowed (K.coreStep (ConnectionManagement.OutboundMachine.beginAcquire w req)) (W.source s)
... | false = refl
... | true = refl

module SelfPurge where
  v0 : Outer
  v0 = embed F.s0 unread
  v1 : Outer
  v1 = embed F.s1 unread
  e1 : outerStep (label F.a1) v0 ≡ just v1
  e1 = refl
  v2 : Outer
  v2 = embed F.s2 unread
  e2 : outerStep (label F.a2) v1 ≡ just v2
  e2 = refl
  v3 : Outer
  v3 = embed F.s3 unread
  e3 : outerStep (label F.a3) v2 ≡ just v3
  e3 = refl
  v4 : Outer
  v4 = embed F.s4 unread
  e4 : outerStep (label F.a4) v3 ≡ just v4
  e4 = refl
  v5 : Outer
  v5 = embed F.s5 unread
  e5 : outerStep (label F.a5) v4 ≡ just v5
  e5 = refl
  v6 : Outer
  v6 = embed F.s6 unread
  e6 : outerStep (label F.a6) v5 ≡ just v6
  e6 = refl
  v7 : Outer
  v7 = embed F.s7 unread
  e7 : outerStep (label F.a7) v6 ≡ just v7
  e7 = refl
  v8 : Outer
  v8 = embed F.s8 unread
  e8 : outerStep (label F.a8) v7 ≡ just v8
  e8 = refl
  v9 : Outer
  v9 = embed F.s9 unread
  e9 : outerStep (label F.a9) v8 ≡ just v9
  e9 = refl
  v10 : Outer
  v10 = embed F.s10 unread
  e10 : outerStep (label F.a10) v9 ≡ just v10
  e10 = refl
  v11 : Outer
  v11 = embed F.s11 unread
  e11 : outerStep (label F.a11) v10 ≡ just v11
  e11 = refl
  v12 : Outer
  v12 = embed F.s12 unread
  e12 : outerStep (label F.a12) v11 ≡ just v12
  e12 = refl
  v13 : Outer
  v13 = embed F.s13 unread
  e13 : outerStep (label F.a13) v12 ≡ just v13
  e13 = refl
  v14 : Outer
  v14 = embed F.s14 unread
  e14 : outerStep (label F.a14) v13 ≡ just v14
  e14 = refl
  v15 : Outer
  v15 = embed F.s15 unread
  e15 : outerStep (label F.a15) v14 ≡ just v15
  e15 = refl
  v16 : Outer
  v16 = embed F.s16 unread
  e16 : outerStep (label F.a16) v15 ≡ just v16
  e16 = refl
  v17 : Outer
  v17 = embed F.s17 unread
  e17 : outerStep (label F.a17) v16 ≡ just v17
  e17 = refl
  v18 : Outer
  v18 = embed F.s18 unread
  e18 : outerStep (label F.a18) v17 ≡ just v18
  e18 = refl
  v19 : Outer
  v19 = embed F.s19 unread
  e19 : outerStep (label F.a19) v18 ≡ just v19
  e19 = refl
  v20 : Outer
  v20 = embed F.s20 unread
  e20 : outerStep (label F.a20) v19 ≡ just v20
  e20 = refl
  v21 : Outer
  v21 = embed F.s21 unread
  e21 : outerStep (label F.a21) v20 ≡ just v21
  e21 = refl
  v22 : Outer
  v22 = embed F.s22 unread
  e22 : outerStep (label F.a22) v21 ≡ just v22
  e22 = refl
  v23 : Outer
  v23 = embed F.s23 unread
  e23 : outerStep (label F.a23) v22 ≡ just v23
  e23 = refl
  v24 : Outer
  v24 = embed F.s24 unread
  e24 : outerStep (label F.a24) v23 ≡ just v24
  e24 = refl
  v25 : Outer
  v25 = embed F.s25 unread
  e25 : outerStep (label F.a25) v24 ≡ just v25
  e25 = refl
  v26 : Outer
  v26 = embed F.s26 unread
  e26 : outerStep (label F.a26) v25 ≡ just v26
  e26 = refl
  v27 : Outer
  v27 = embed F.s27 unread
  e27 : outerStep (label F.a27) v26 ≡ just v27
  e27 = refl
  v28 : Outer
  v28 = embed F.s28 unread
  e28 : outerStep (label F.a28) v27 ≡ just v28
  e28 = refl
  v29 : Outer
  v29 = embed F.s29 unread
  e29 : outerStep (label F.a29) v28 ≡ just v29
  e29 = refl
  v30 : Outer
  v30 = embed F.s30 unread
  e30 : outerStep (label F.a30) v29 ≡ just v30
  e30 = refl
  v31 : Outer
  v31 = embed F.s31 unread
  e31 : outerStep (label F.a31) v30 ≡ just v31
  e31 = refl
  v32 : Outer
  v32 = embed F.s32 unread
  e32 : outerStep (label F.a32) v31 ≡ just v32
  e32 = refl
  v33 : Outer
  v33 = embed F.s33 unread
  e33 : outerStep (label F.a33) v32 ≡ just v33
  e33 = refl
  v34 : Outer
  v34 = embed F.s34 unread
  e34 : outerStep (label F.a34) v33 ≡ just v34
  e34 = refl
  v35 : Outer
  v35 = embed F.s35 unread
  e35 : outerStep (label F.a35) v34 ≡ just v35
  e35 = refl
  v36 : Outer
  v36 = embed F.s36 unread
  e36 : outerStep (label F.a36) v35 ≡ just v36
  e36 = refl
  v37 : Outer
  v37 = embed F.s37 unread
  e37 : outerStep (label F.a37) v36 ≡ just v37
  e37 = refl
  v38 : Outer
  v38 = embed F.s38 unread
  e38 : outerStep (label F.a38) v37 ≡ just v38
  e38 = refl
  v39 : Outer
  v39 = embed F.s39 unread
  e39 : outerStep (label F.a39) v38 ≡ just v39
  e39 = refl
  v40 : Outer
  v40 = embed F.s40 unread
  e40 : outerStep (label F.a40) v39 ≡ just v40
  e40 = refl
  v41 : Outer
  v41 = embed F.s41 unread
  e41 : outerStep (label F.a41) v40 ≡ just v41
  e41 = refl
  v42 : Outer
  v42 = embed F.s42 unread
  e42 : outerStep (label F.a42) v41 ≡ just v42
  e42 = refl
  v43 : Outer
  v43 = embed F.s43 unread
  e43 : outerStep (label F.a43) v42 ≡ just v43
  e43 = refl
  v44 : Outer
  v44 = embed F.s44 unread
  e44 : outerStep (label F.a44) v43 ≡ just v44
  e44 = refl
  v45 : Outer
  v45 = embed F.s45 unread
  e45 : outerStep (label F.a45) v44 ≡ just v45
  e45 = refl
  v46 : Outer
  v46 = embed F.s46 unread
  e46 : outerStep (label F.a46) v45 ≡ just v46
  e46 = refl
  v47 : Outer
  v47 = embed F.s47 unread
  e47 : outerStep (label F.a47) v46 ≡ just v47
  e47 = refl
  v48 : Outer
  v48 = embed F.s48 unread
  e48 : outerStep (label F.a48) v47 ≡ just v48
  e48 = refl
  v49 : Outer
  v49 = embed F.s49 unread
  e49 : outerStep (label F.a49) v48 ≡ just v49
  e49 = refl
  v50 : Outer
  v50 = embed F.s50 unread
  e50 : outerStep (label F.a50) v49 ≡ just v50
  e50 = refl
  v51 : Outer
  v51 = embed F.s51 unread
  e51 : outerStep (label F.a51) v50 ≡ just v51
  e51 = refl
  v52 : Outer
  v52 = embed F.s52 unread
  e52 : outerStep (label F.a52) v51 ≡ just v52
  e52 = refl
  v53 : Outer
  v53 = embed F.s53 unread
  e53 : outerStep (label F.a53) v52 ≡ just v53
  e53 = refl
  v54 : Outer
  v54 = embed F.s54 unread
  e54 : outerStep (label F.a54) v53 ≡ just v54
  e54 = refl
  v55 : Outer
  v55 = embed F.s55 unread
  e55 : outerStep (label F.a55) v54 ≡ just v55
  e55 = refl
  v56 : Outer
  v56 = embed F.s56 unread
  e56 : outerStep (label F.a56) v55 ≡ just v56
  e56 = refl
  v57 : Outer
  v57 = embed F.s57 unread
  e57 : outerStep (label F.a57) v56 ≡ just v57
  e57 = refl
  v58 : Outer
  v58 = embed F.s58 unread
  e58 : outerStep (label F.a58) v57 ≡ just v58
  e58 = refl
  v59 : Outer
  v59 = embed F.s59 unread
  e59 : outerStep (label F.a59) v58 ≡ just v59
  e59 = refl
  v60 : Outer
  v60 = embed F.s60 unread
  e60 : outerStep (label F.a60) v59 ≡ just v60
  e60 = refl
  v61 : Outer
  v61 = embed F.s61 unread
  e61 : outerStep (label F.a61) v60 ≡ just v61
  e61 = refl
  v62 : Outer
  v62 = embed F.s62 unread
  e62 : outerStep (label F.a62) v61 ≡ just v62
  e62 = refl
  v63 : Outer
  v63 = embed F.s63 unread
  e63 : outerStep (label F.a63) v62 ≡ just v63
  e63 = refl
  v64 : Outer
  v64 = embed F.s64 unread
  e64 : outerStep (label F.a64) v63 ≡ just v64
  e64 = refl
  v65 : Outer
  v65 = embed F.s65 unread
  e65 : outerStep (label F.a65) v64 ≡ just v65
  e65 = refl
  v66 : Outer
  v66 = embed F.s66 unread
  e66 : outerStep (label F.a66) v65 ≡ just v66
  e66 = refl
  v67 : Outer
  v67 = embed F.s67 unread
  e67 : outerStep (label F.a67) v66 ≡ just v67
  e67 = refl
  v68 : Outer
  v68 = embed F.s68 unread
  e68 : outerStep (label F.a68) v67 ≡ just v68
  e68 = refl
  v69 : Outer
  v69 = embed F.s69 unread
  e69 : outerStep (label F.a69) v68 ≡ just v69
  e69 = refl
  v70 : Outer
  v70 = embed F.s70 unread
  e70 : outerStep (label F.a70) v69 ≡ just v70
  e70 = refl
  v71 : Outer
  v71 = embed F.s71 unread
  e71 : outerStep (label F.a71) v70 ≡ just v71
  e71 = refl
  v72 : Outer
  v72 = embed F.s72 unread
  e72 : outerStep (label F.a72) v71 ≡ just v72
  e72 = refl
  v73 : Outer
  v73 = embed F.s73 unread
  e73 : outerStep (label F.a73) v72 ≡ just v73
  e73 = refl
  v74 : Outer
  v74 = embed F.s74 unread
  e74 : outerStep (label F.a74) v73 ≡ just v74
  e74 = refl
  v75 : Outer
  v75 = embed F.s75 unread
  e75 : outerStep (label F.a75) v74 ≡ just v75
  e75 = refl
  v76 : Outer
  v76 = embed F.s76 unread
  e76 : outerStep (label F.a76) v75 ≡ just v76
  e76 = refl
  v77 : Outer
  v77 = embed F.s77 unread
  e77 : outerStep (label F.a77) v76 ≡ just v77
  e77 = refl
  -- The old run first diverges when the map-only CM tries to finish.
  old-close-refused : outerStep (label F.a78) v77 ≡ nothing
  old-close-refused = refl
  read : Outer
  read = embed F.s77 (scanning (A.child₀ ∷ []) (A.child₀ ∷ []))
  read-edge : outerStep (innerAct readRegistry) v77 ≡ just read
  read-edge = refl
  pending : Outer
  pending = embed F.s77 (sending (A.child₀ ∷ []) A.child₀ [])
  request-edge : outerStep (innerAct requestHandler) read ≡ just pending
  request-edge = refl
  -- Uninterruptible cleanup cannot be interrupted through a handshake label.
  masked-finalizer-refuses-handshake-cancel : outerStep (innerAct (cancelHandler Variant.handshake F.err)) pending ≡ nothing
  masked-finalizer-refuses-handshake-cancel = refl
  not-a-result : outerStep (innerAct acknowledgeHandler) pending ≡ nothing
  not-a-result = refl
  premature-wait : outerStep (innerAct waitHandlers) read ≡ nothing
  premature-wait = refl
  doneWorld : Shared.State
  doneWorld = record (F.cleaned []) { cleanups = (A.child₀ , Shared.cleanupDone Shared.cleanupNormal) ∷ [] }
  doneCore : Machine.Configuration
  doneCore = F.coreOf doneWorld F.installedFlushed
  source1 : W.Outer
  source1 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.finalizing (N.W.peerException F.err)))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k77 S.closingCM false S.igResultAvailable F.resultDone (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h1 : Outer
  h1 = embed source1 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge1 : outerStep (label (F.runW (N.W.cleanup A.child₀ Cleanup.readCleanupCounters))) pending ≡ just h1
  hEdge1 = refl
  source2 : W.Outer
  source2 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.cleanupComplete (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k77 S.closingCM false S.igResultAvailable F.resultDone (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h2 : Outer
  h2 = embed source2 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge2 : outerStep (label (F.runW (N.W.finishCleanup A.child₀))) h1 ≡ just h2
  hEdge2 = refl
  source3 : W.Outer
  source3 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.resultAvailable (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k77 S.closingCM false S.igResultAvailable F.resultDone (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h3 : Outer
  h3 = embed source3 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge3 : outerStep (label (F.runW (N.W.publishAsyncResult A.child₀))) h2 ≡ just h3
  hEdge3 = refl
  acknowledged : Outer
  acknowledged = embed source3 (scanning (A.child₀ ∷ []) [])
  acknowledge-edge : outerStep (innerAct acknowledgeHandler) h3 ≡ just acknowledged
  acknowledge-edge = refl
  waitedState : Outer
  waitedState = embed source3 (waited (A.child₀ ∷ []))
  wait-edge : outerStep (innerAct waitHandlers) acknowledged ≡ just waitedState
  wait-edge = refl
  repaired78 : W.Outer
  repaired78 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.resultAvailable (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k78 S.closingCM false S.igResultAvailable F.resultDone (Close.shutdownState Close.closed [] [] []) (RR.initial true)
  v78 : Outer
  v78 = embed repaired78 (waited (A.child₀ ∷ []))
  e78 : outerStep (label F.a78) waitedState ≡ just v78
  e78 = refl
  repaired79 : W.Outer
  repaired79 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.resultAvailable (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k79 S.serverReturned false S.igResultAvailable F.resultDone (Close.shutdownState Close.closed [] [] []) (RR.initial true)
  v79 : Outer
  v79 = embed repaired79 (waited (A.child₀ ∷ []))
  e79 : outerStep (label F.a79) v78 ≡ just v79
  e79 = refl
  repaired80 : W.Outer
  repaired80 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.resultAvailable (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k80 S.serverReturned false S.igResultAvailable F.resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.cancelRequested) RR.cancelling)
  v80 : Outer
  v80 = embed repaired80 (waited (A.child₀ ∷ []))
  e80 : outerStep (label F.a80) v79 ≡ just v80
  e80 = refl
  repaired81 : W.Outer
  repaired81 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.resultAvailable (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k81 S.serverReturned false S.igResultAvailable F.resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.cancelDelivered) RR.cancelling)
  v81 : Outer
  v81 = embed repaired81 (waited (A.child₀ ∷ []))
  e81 : outerStep (label F.a81) v80 ≡ just v81
  e81 = refl
  repaired82 : W.Outer
  repaired82 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.resultAvailable (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k82 S.serverReturned false S.igResultAvailable F.resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.bodyExited) RR.cancelling)
  v82 : Outer
  v82 = embed repaired82 (waited (A.child₀ ∷ []))
  e82 : outerStep (label F.a82) v81 ≡ just v82
  e82 = refl
  repaired83 : W.Outer
  repaired83 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.resultAvailable (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k83 S.serverReturned false S.igResultAvailable F.resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.resultAvailable) RR.cancelling)
  v83 : Outer
  v83 = embed repaired83 (waited (A.child₀ ∷ []))
  e83 : outerStep (label F.a83) v82 ≡ just v83
  e83 = refl
  repaired84 : W.Outer
  repaired84 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.resultAvailable (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k84 S.serverReturned false S.igResultAvailable F.resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.joined) RR.cancelling)
  v84 : Outer
  v84 = embed repaired84 (waited (A.child₀ ∷ []))
  e84 : outerStep (label F.a84) v83 ≡ just v84
  e84 = refl
  repaired85 : W.Outer
  repaired85 = F.render doneCore (just H.handshaking) (just (F.frame (N.U.promisePublished (ident 0) (ident 0)) (N.S.startupState N.S.published N.Pool.initial))) (just N.R.handedOff) (just (N.W.resultAvailable (N.W.peerException F.err) Shared.cleanupNormal))
    ((A.w₀ , S.rawWorker A.r₀ (S.resultAvailable S.returned) 0) ∷ []) ((A.w₀ , true) ∷ []) F.k85 S.serverReturned false S.igResultAvailable F.resultDone (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.joined) RR.finished)
  v85 : Outer
  v85 = embed repaired85 (waited (A.child₀ ∷ []))
  e85 : outerStep (label F.a85) v84 ≡ just v85
  e85 = refl
  actions : List OuterAction
  actions = label F.a1 ∷ label F.a2 ∷ label F.a3 ∷ label F.a4 ∷ label F.a5 ∷ label F.a6 ∷ label F.a7 ∷ label F.a8 ∷ label F.a9 ∷ label F.a10 ∷ label F.a11 ∷ label F.a12 ∷ label F.a13 ∷ label F.a14 ∷ label F.a15 ∷ label F.a16 ∷ label F.a17 ∷ label F.a18 ∷ label F.a19 ∷ label F.a20 ∷ label F.a21 ∷ label F.a22 ∷ label F.a23 ∷ label F.a24 ∷ label F.a25 ∷ label F.a26 ∷ label F.a27 ∷ label F.a28 ∷ label F.a29 ∷ label F.a30 ∷ label F.a31 ∷ label F.a32 ∷ label F.a33 ∷ label F.a34 ∷ label F.a35 ∷ label F.a36 ∷ label F.a37 ∷ label F.a38 ∷ label F.a39 ∷ label F.a40 ∷ label F.a41 ∷ label F.a42 ∷ label F.a43 ∷ label F.a44 ∷ label F.a45 ∷ label F.a46 ∷ label F.a47 ∷ label F.a48 ∷ label F.a49 ∷ label F.a50 ∷ label F.a51 ∷ label F.a52 ∷ label F.a53 ∷ label F.a54 ∷ label F.a55 ∷ label F.a56 ∷ label F.a57 ∷ label F.a58 ∷ label F.a59 ∷ label F.a60 ∷ label F.a61 ∷ label F.a62 ∷ label F.a63 ∷ label F.a64 ∷ label F.a65 ∷ label F.a66 ∷ label F.a67 ∷ label F.a68 ∷ label F.a69 ∷ label F.a70 ∷ label F.a71 ∷ label F.a72 ∷ label F.a73 ∷ label F.a74 ∷ label F.a75 ∷ label F.a76 ∷ label F.a77 ∷ innerAct readRegistry ∷ innerAct requestHandler ∷ label (F.runW (N.W.cleanup A.child₀ Cleanup.readCleanupCounters)) ∷ label (F.runW (N.W.finishCleanup A.child₀)) ∷ label (F.runW (N.W.publishAsyncResult A.child₀)) ∷ innerAct acknowledgeHandler ∷ innerAct waitHandlers ∷ label F.a78 ∷ label F.a79 ∷ label F.a80 ∷ label F.a81 ∷ label F.a82 ∷ label F.a83 ∷ label F.a84 ∷ label F.a85 ∷ []
  initializer : T.initialize (ConnectionManagement.OutboundMachine.initial F.c₀) F.settings ≡ just F.initial
  initializer = refl
  initialized-start : v0 ≡ outer (initial F.initial) (RR.initial true)
  initialized-start = refl
  abstract
    progress-run : Executes v0 actions v85
    progress-run = next e1 (next e2 (next e3 (next e4 (next e5 (next e6 (next e7 (next e8 (next e9 (next e10 (next e11 (next e12 (next e13 (next e14 (next e15 (next e16 (next e17 (next e18 (next e19 (next e20 (next e21 (next e22 (next e23 (next e24 (next e25 (next e26 (next e27 (next e28 (next e29 (next e30 (next e31 (next e32 (next e33 (next e34 (next e35 (next e36 (next e37 (next e38 (next e39 (next e40 (next e41 (next e42 (next e43 (next e44 (next e45 (next e46 (next e47 (next e48 (next e49 (next e50 (next e51 (next e52 (next e53 (next e54 (next e55 (next e56 (next e57 (next e58 (next e59 (next e60 (next e61 (next e62 (next e63 (next e64 (next e65 (next e66 (next e67 (next e68 (next e69 (next e70 (next e71 (next e72 (next e73 (next e74 (next e75 (next e76 (next e77 (next read-edge (next request-edge (next hEdge1 (next hEdge2 (next hEdge3 (next acknowledge-edge (next wait-edge (next e78 (next e79 (next e80 (next e81 (next e82 (next e83 (next e84 (next e85 (done))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  finished : RR.owner (relays v85) ≡ RR.finished
  finished = refl
  quiescent : Quiescent (inner v85)
  quiescent = quiescence {c₀ = F.c₀} {g = F.settings} {start = F.initial} {scheduled = true} {as = actions} {final = inner v85} {t = just RR.joined} initializer progress-run
  physical-result : ready (base (inner v85)) A.child₀ ≡ true
  physical-result = refl

module FailedHandshake where
  v0 : Outer
  v0 = embed C.s0 unread
  v1 : Outer
  v1 = embed C.s1 unread
  e1 : outerStep (label C.a1) v0 ≡ just v1
  e1 = refl
  v2 : Outer
  v2 = embed C.s2 unread
  e2 : outerStep (label C.a2) v1 ≡ just v2
  e2 = refl
  v3 : Outer
  v3 = embed C.s3 unread
  e3 : outerStep (label C.a3) v2 ≡ just v3
  e3 = refl
  v4 : Outer
  v4 = embed C.s4 unread
  e4 : outerStep (label C.a4) v3 ≡ just v4
  e4 = refl
  v5 : Outer
  v5 = embed C.s5 unread
  e5 : outerStep (label C.a5) v4 ≡ just v5
  e5 = refl
  v6 : Outer
  v6 = embed C.s6 unread
  e6 : outerStep (label C.a6) v5 ≡ just v6
  e6 = refl
  v7 : Outer
  v7 = embed C.s7 unread
  e7 : outerStep (label C.a7) v6 ≡ just v7
  e7 = refl
  v8 : Outer
  v8 = embed C.s8 unread
  e8 : outerStep (label C.a8) v7 ≡ just v8
  e8 = refl
  v9 : Outer
  v9 = embed C.s9 unread
  e9 : outerStep (label C.a9) v8 ≡ just v9
  e9 = refl
  v10 : Outer
  v10 = embed C.s10 unread
  e10 : outerStep (label C.a10) v9 ≡ just v10
  e10 = refl
  v11 : Outer
  v11 = embed C.s11 unread
  e11 : outerStep (label C.a11) v10 ≡ just v11
  e11 = refl
  v12 : Outer
  v12 = embed C.s12 unread
  e12 : outerStep (label C.a12) v11 ≡ just v12
  e12 = refl
  v13 : Outer
  v13 = embed C.s13 unread
  e13 : outerStep (label C.a13) v12 ≡ just v13
  e13 = refl
  v14 : Outer
  v14 = embed C.s14 unread
  e14 : outerStep (label C.a14) v13 ≡ just v14
  e14 = refl
  v15 : Outer
  v15 = embed C.s15 unread
  e15 : outerStep (label C.a15) v14 ≡ just v15
  e15 = refl
  v16 : Outer
  v16 = embed C.s16 unread
  e16 : outerStep (label C.a16) v15 ≡ just v16
  e16 = refl
  v17 : Outer
  v17 = embed C.s17 unread
  e17 : outerStep (label C.a17) v16 ≡ just v17
  e17 = refl
  v18 : Outer
  v18 = embed C.s18 unread
  e18 : outerStep (label C.a18) v17 ≡ just v18
  e18 = refl
  v19 : Outer
  v19 = embed C.s19 unread
  e19 : outerStep (label C.a19) v18 ≡ just v19
  e19 = refl
  v20 : Outer
  v20 = embed C.s20 unread
  e20 : outerStep (label C.a20) v19 ≡ just v20
  e20 = refl
  v21 : Outer
  v21 = embed C.s21 unread
  e21 : outerStep (label C.a21) v20 ≡ just v21
  e21 = refl
  v22 : Outer
  v22 = embed C.s22 unread
  e22 : outerStep (label C.a22) v21 ≡ just v22
  e22 = refl
  v23 : Outer
  v23 = embed C.s23 unread
  e23 : outerStep (label C.a23) v22 ≡ just v23
  e23 = refl
  v24 : Outer
  v24 = embed C.s24 unread
  e24 : outerStep (label C.a24) v23 ≡ just v24
  e24 = refl
  v25 : Outer
  v25 = embed C.s25 unread
  e25 : outerStep (label C.a25) v24 ≡ just v25
  e25 = refl
  v26 : Outer
  v26 = embed C.s26 unread
  e26 : outerStep (label C.a26) v25 ≡ just v26
  e26 = refl
  v27 : Outer
  v27 = embed C.s27 unread
  e27 : outerStep (label C.a27) v26 ≡ just v27
  e27 = refl
  v28 : Outer
  v28 = embed C.s28 unread
  e28 : outerStep (label C.a28) v27 ≡ just v28
  e28 = refl
  v29 : Outer
  v29 = embed C.s29 unread
  e29 : outerStep (label C.a29) v28 ≡ just v29
  e29 = refl
  v30 : Outer
  v30 = embed C.s30 unread
  e30 : outerStep (label C.a30) v29 ≡ just v30
  e30 = refl
  v31 : Outer
  v31 = embed C.s31 unread
  e31 : outerStep (label C.a31) v30 ≡ just v31
  e31 = refl
  v32 : Outer
  v32 = embed C.s32 unread
  e32 : outerStep (label C.a32) v31 ≡ just v32
  e32 = refl
  v33 : Outer
  v33 = embed C.s33 unread
  e33 : outerStep (label C.a33) v32 ≡ just v33
  e33 = refl
  v34 : Outer
  v34 = embed C.s34 unread
  e34 : outerStep (label C.a34) v33 ≡ just v34
  e34 = refl
  v35 : Outer
  v35 = embed C.s35 unread
  e35 : outerStep (label C.a35) v34 ≡ just v35
  e35 = refl
  v36 : Outer
  v36 = embed C.s36 unread
  e36 : outerStep (label C.a36) v35 ≡ just v36
  e36 = refl
  v37 : Outer
  v37 = embed C.s37 unread
  e37 : outerStep (label C.a37) v36 ≡ just v37
  e37 = refl
  v38 : Outer
  v38 = embed C.s38 unread
  e38 : outerStep (label C.a38) v37 ≡ just v38
  e38 = refl
  v39 : Outer
  v39 = embed C.s39 unread
  e39 : outerStep (label C.a39) v38 ≡ just v39
  e39 = refl
  v40 : Outer
  v40 = embed C.s40 unread
  e40 : outerStep (label C.a40) v39 ≡ just v40
  e40 = refl
  v41 : Outer
  v41 = embed C.s41 unread
  e41 : outerStep (label C.a41) v40 ≡ just v41
  e41 = refl
  v42 : Outer
  v42 = embed C.s42 unread
  e42 : outerStep (label C.a42) v41 ≡ just v42
  e42 = refl
  v43 : Outer
  v43 = embed C.s43 unread
  e43 : outerStep (label C.a43) v42 ≡ just v43
  e43 = refl
  v44 : Outer
  v44 = embed C.s44 unread
  e44 : outerStep (label C.a44) v43 ≡ just v44
  e44 = refl
  v45 : Outer
  v45 = embed C.s45 unread
  e45 : outerStep (label C.a45) v44 ≡ just v45
  e45 = refl
  v46 : Outer
  v46 = embed C.s46 unread
  e46 : outerStep (label C.a46) v45 ≡ just v46
  e46 = refl
  v47 : Outer
  v47 = embed C.s47 unread
  e47 : outerStep (label C.a47) v46 ≡ just v47
  e47 = refl
  v48 : Outer
  v48 = embed C.s48 unread
  e48 : outerStep (label C.a48) v47 ≡ just v48
  e48 = refl
  v49 : Outer
  v49 = embed C.s49 unread
  e49 : outerStep (label C.a49) v48 ≡ just v49
  e49 = refl
  v50 : Outer
  v50 = embed C.s50 unread
  e50 : outerStep (label C.a50) v49 ≡ just v50
  e50 = refl
  v51 : Outer
  v51 = embed C.s51 unread
  e51 : outerStep (label C.a51) v50 ≡ just v51
  e51 = refl
  v52 : Outer
  v52 = embed C.s52 unread
  e52 : outerStep (label C.a52) v51 ≡ just v52
  e52 = refl
  v53 : Outer
  v53 = embed C.s53 unread
  e53 : outerStep (label C.a53) v52 ≡ just v53
  e53 = refl
  v54 : Outer
  v54 = embed C.s54 unread
  e54 : outerStep (label C.a54) v53 ≡ just v54
  e54 = refl
  v55 : Outer
  v55 = embed C.s55 unread
  e55 : outerStep (label C.a55) v54 ≡ just v55
  e55 = refl
  v56 : Outer
  v56 = embed C.s56 unread
  e56 : outerStep (label C.a56) v55 ≡ just v56
  e56 = refl
  v57 : Outer
  v57 = embed C.s57 unread
  e57 : outerStep (label C.a57) v56 ≡ just v57
  e57 = refl
  v58 : Outer
  v58 = embed C.s58 unread
  e58 : outerStep (label C.a58) v57 ≡ just v58
  e58 = refl
  v59 : Outer
  v59 = embed C.s59 unread
  e59 : outerStep (label C.a59) v58 ≡ just v59
  e59 = refl
  v60 : Outer
  v60 = embed C.s60 unread
  e60 : outerStep (label C.a60) v59 ≡ just v60
  e60 = refl
  v61 : Outer
  v61 = embed C.s61 unread
  e61 : outerStep (label C.a61) v60 ≡ just v61
  e61 = refl
  v62 : Outer
  v62 = embed C.s62 unread
  e62 : outerStep (label C.a62) v61 ≡ just v62
  e62 = refl
  v63 : Outer
  v63 = embed C.s63 unread
  e63 : outerStep (label C.a63) v62 ≡ just v63
  e63 = refl
  v64 : Outer
  v64 = embed C.s64 unread
  e64 : outerStep (label C.a64) v63 ≡ just v64
  e64 = refl
  v65 : Outer
  v65 = embed C.s65 unread
  e65 : outerStep (label C.a65) v64 ≡ just v65
  e65 = refl
  v66 : Outer
  v66 = embed C.s66 unread
  e66 : outerStep (label C.a66) v65 ≡ just v66
  e66 = refl
  -- The old run first diverges when the map-only CM tries to finish.
  old-close-refused : outerStep (label C.a67) v66 ≡ nothing
  old-close-refused = refl
  read : Outer
  read = embed C.s66 (scanning (A.child₀ ∷ []) (A.child₀ ∷ []))
  read-edge : outerStep (innerAct readRegistry) v66 ≡ just read
  read-edge = refl
  pending : Outer
  pending = embed C.s66 (sending (A.child₀ ∷ []) A.child₀ [])
  request-edge : outerStep (innerAct requestHandler) read ≡ just pending
  request-edge = refl
  not-a-result : outerStep (innerAct acknowledgeHandler) pending ≡ nothing
  not-a-result = refl
  premature-wait : outerStep (innerAct waitHandlers) read ≡ nothing
  premature-wait = refl
  cleanupLease : Shared.Lease
  cleanupLease = Shared.lease A.child₀ []
  cleanupWorld : Shared.MapCell → Shared.CleanupPC → Shared.State
  cleanupWorld cell pc = record C.w17 { cm = Shared.cmStore cell ((ident 0 , Shared.terminated (just C.err)) ∷ []) 1
    ; cleanups = (A.child₀ , pc) ∷ [] }
  doneWorld : Shared.State
  doneWorld = cleanupWorld (Shared.full []) (Shared.cleanupDone Shared.cleanupNormal)
  source1 : W.Outer
  source1 = C.render (C.w17) (just (H.bodyExited C.err)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k66 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h1 : Outer
  h1 = embed source1 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge1 : outerStep (label (C.handler (H.rethrowCaught A.child₀))) pending ≡ just h1
  hEdge1 = refl
  source2 : W.Outer
  source2 = C.render (cleanupWorld (Shared.full []) Shared.cleanupAcquire) (just (H.finalizing C.err)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k66 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h2 : Outer
  h2 = embed source2 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge2 : outerStep (label (C.handler (H.enterFinalizer A.child₀))) h1 ≡ just h2
  hEdge2 = refl
  source3 : W.Outer
  source3 = C.render (cleanupWorld (Shared.taken A.child₀) (Shared.cleanupSelect cleanupLease)) (just (H.finalizing C.err)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k66 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h3 : Outer
  h3 = embed source3 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge3 : outerStep (label (C.handler (H.cleanup A.child₀ Cleanup.takeCleanupMap))) h2 ≡ just h3
  hEdge3 = refl
  source4 : W.Outer
  source4 = C.render (cleanupWorld (Shared.taken A.child₀) (Shared.cleanupClose cleanupLease [] Shared.countImmediately)) (just (H.finalizing C.err)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k66 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h4 : Outer
  h4 = embed source4 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge4 : outerStep (label (C.handler (H.cleanup A.child₀ Cleanup.selectCleanupEntry))) h3 ≡ just h4
  hEdge4 = refl
  source5 : W.Outer
  source5 = C.render (cleanupWorld (Shared.taken A.child₀) (Shared.cleanupPublish cleanupLease [] Shared.countImmediately)) (just (H.finalizing C.err)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k66 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h5 : Outer
  h5 = embed source5 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge5 : outerStep (label (C.handler (H.cleanup A.child₀ Cleanup.closeHandlerSocket))) h4 ≡ just h5
  hEdge5 = refl
  source6 : W.Outer
  source6 = C.render (cleanupWorld (Shared.full []) (Shared.cleanupCount Shared.cleanupNormal)) (just (H.finalizing C.err)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k66 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h6 : Outer
  h6 = embed source6 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge6 : outerStep (label (C.handler (H.cleanup A.child₀ Cleanup.publishCleanupMap))) h5 ≡ just h6
  hEdge6 = refl
  source7 : W.Outer
  source7 = C.render (doneWorld) (just (H.finalizing C.err)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k66 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h7 : Outer
  h7 = embed source7 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge7 : outerStep (label (C.handler (H.cleanup A.child₀ Cleanup.readCleanupCounters))) h6 ≡ just h7
  hEdge7 = refl
  source8 : W.Outer
  source8 = C.render (doneWorld) (just (H.cleanupComplete C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k66 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h8 : Outer
  h8 = embed source8 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge8 : outerStep (label (C.handler (H.finishCleanup A.child₀))) h7 ≡ just h8
  hEdge8 = refl
  source9 : W.Outer
  source9 = C.render (doneWorld) (just (H.resultAvailable C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k66 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.awaitResults [] [] []) (RR.initial true)
  h9 : Outer
  h9 = embed source9 (sending (A.child₀ ∷ []) A.child₀ [])
  hEdge9 : outerStep (label (C.handler (H.publishAsyncResult A.child₀))) h8 ≡ just h9
  hEdge9 = refl
  acknowledged : Outer
  acknowledged = embed source9 (scanning (A.child₀ ∷ []) [])
  acknowledge-edge : outerStep (innerAct acknowledgeHandler) h9 ≡ just acknowledged
  acknowledge-edge = refl
  waitedState : Outer
  waitedState = embed source9 (waited (A.child₀ ∷ []))
  wait-edge : outerStep (innerAct waitHandlers) acknowledged ≡ just waitedState
  wait-edge = refl
  repaired67 : W.Outer
  repaired67 = C.render doneWorld (just (H.resultAvailable C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k67 S.closingCM false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.closed [] [] []) (RR.initial true)
  v67 : Outer
  v67 = embed repaired67 (waited (A.child₀ ∷ []))
  e67 : outerStep (label C.a67) waitedState ≡ just v67
  e67 = refl
  repaired68 : W.Outer
  repaired68 = C.render doneWorld (just (H.resultAvailable C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k68 S.serverReturned false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.closed [] [] []) (RR.initial true)
  v68 : Outer
  v68 = embed repaired68 (waited (A.child₀ ∷ []))
  e68 : outerStep (label C.a68) v67 ≡ just v68
  e68 = refl
  repaired69 : W.Outer
  repaired69 = C.render doneWorld (just (H.resultAvailable C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k69 S.serverReturned false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.cancelRequested) RR.cancelling)
  v69 : Outer
  v69 = embed repaired69 (waited (A.child₀ ∷ []))
  e69 : outerStep (label C.a69) v68 ≡ just v69
  e69 = refl
  repaired70 : W.Outer
  repaired70 = C.render doneWorld (just (H.resultAvailable C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k70 S.serverReturned false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.cancelDelivered) RR.cancelling)
  v70 : Outer
  v70 = embed repaired70 (waited (A.child₀ ∷ []))
  e70 : outerStep (label C.a70) v69 ≡ just v70
  e70 = refl
  repaired71 : W.Outer
  repaired71 = C.render doneWorld (just (H.resultAvailable C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k71 S.serverReturned false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.bodyExited) RR.cancelling)
  v71 : Outer
  v71 = embed repaired71 (waited (A.child₀ ∷ []))
  e71 : outerStep (label C.a71) v70 ≡ just v71
  e71 = refl
  repaired72 : W.Outer
  repaired72 = C.render doneWorld (just (H.resultAvailable C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k72 S.serverReturned false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.resultAvailable) RR.cancelling)
  v72 : Outer
  v72 = embed repaired72 (waited (A.child₀ ∷ []))
  e72 : outerStep (label C.a72) v71 ≡ just v72
  e72 = refl
  repaired73 : W.Outer
  repaired73 = C.render doneWorld (just (H.resultAvailable C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k73 S.serverReturned false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.joined) RR.cancelling)
  v73 : Outer
  v73 = embed repaired73 (waited (A.child₀ ∷ []))
  e73 : outerStep (label C.a73) v72 ≡ just v73
  e73 = refl
  repaired74 : W.Outer
  repaired74 = C.render doneWorld (just (H.resultAvailable C.err Shared.cleanupNormal)) (C.closedWorkers (S.resultAvailable S.returned)) ((A.w₀ , true) ∷ []) C.k74 S.serverReturned false S.igResultAvailable C.resultDone C.igFlushed (Close.shutdownState Close.closed [] [] []) (RR.relaysState (just RR.joined) RR.finished)
  v74 : Outer
  v74 = embed repaired74 (waited (A.child₀ ∷ []))
  e74 : outerStep (label C.a74) v73 ≡ just v74
  e74 = refl
  actions : List OuterAction
  actions = label C.a1 ∷ label C.a2 ∷ label C.a3 ∷ label C.a4 ∷ label C.a5 ∷ label C.a6 ∷ label C.a7 ∷ label C.a8 ∷ label C.a9 ∷ label C.a10 ∷ label C.a11 ∷ label C.a12 ∷ label C.a13 ∷ label C.a14 ∷ label C.a15 ∷ label C.a16 ∷ label C.a17 ∷ label C.a18 ∷ label C.a19 ∷ label C.a20 ∷ label C.a21 ∷ label C.a22 ∷ label C.a23 ∷ label C.a24 ∷ label C.a25 ∷ label C.a26 ∷ label C.a27 ∷ label C.a28 ∷ label C.a29 ∷ label C.a30 ∷ label C.a31 ∷ label C.a32 ∷ label C.a33 ∷ label C.a34 ∷ label C.a35 ∷ label C.a36 ∷ label C.a37 ∷ label C.a38 ∷ label C.a39 ∷ label C.a40 ∷ label C.a41 ∷ label C.a42 ∷ label C.a43 ∷ label C.a44 ∷ label C.a45 ∷ label C.a46 ∷ label C.a47 ∷ label C.a48 ∷ label C.a49 ∷ label C.a50 ∷ label C.a51 ∷ label C.a52 ∷ label C.a53 ∷ label C.a54 ∷ label C.a55 ∷ label C.a56 ∷ label C.a57 ∷ label C.a58 ∷ label C.a59 ∷ label C.a60 ∷ label C.a61 ∷ label C.a62 ∷ label C.a63 ∷ label C.a64 ∷ label C.a65 ∷ label C.a66 ∷ innerAct readRegistry ∷ innerAct requestHandler ∷ label (C.handler (H.rethrowCaught A.child₀)) ∷ label (C.handler (H.enterFinalizer A.child₀)) ∷ label (C.handler (H.cleanup A.child₀ Cleanup.takeCleanupMap)) ∷ label (C.handler (H.cleanup A.child₀ Cleanup.selectCleanupEntry)) ∷ label (C.handler (H.cleanup A.child₀ Cleanup.closeHandlerSocket)) ∷ label (C.handler (H.cleanup A.child₀ Cleanup.publishCleanupMap)) ∷ label (C.handler (H.cleanup A.child₀ Cleanup.readCleanupCounters)) ∷ label (C.handler (H.finishCleanup A.child₀)) ∷ label (C.handler (H.publishAsyncResult A.child₀)) ∷ innerAct acknowledgeHandler ∷ innerAct waitHandlers ∷ label C.a67 ∷ label C.a68 ∷ label C.a69 ∷ label C.a70 ∷ label C.a71 ∷ label C.a72 ∷ label C.a73 ∷ label C.a74 ∷ []
  initializer : T.initialize (ConnectionManagement.OutboundMachine.initial C.c₀) C.settings ≡ just C.initial
  initializer = refl
  initialized-start : v0 ≡ outer (initial C.initial) (RR.initial true)
  initialized-start = refl
  abstract
    progress-run : Executes v0 actions v74
    progress-run = next e1 (next e2 (next e3 (next e4 (next e5 (next e6 (next e7 (next e8 (next e9 (next e10 (next e11 (next e12 (next e13 (next e14 (next e15 (next e16 (next e17 (next e18 (next e19 (next e20 (next e21 (next e22 (next e23 (next e24 (next e25 (next e26 (next e27 (next e28 (next e29 (next e30 (next e31 (next e32 (next e33 (next e34 (next e35 (next e36 (next e37 (next e38 (next e39 (next e40 (next e41 (next e42 (next e43 (next e44 (next e45 (next e46 (next e47 (next e48 (next e49 (next e50 (next e51 (next e52 (next e53 (next e54 (next e55 (next e56 (next e57 (next e58 (next e59 (next e60 (next e61 (next e62 (next e63 (next e64 (next e65 (next e66 (next read-edge (next request-edge (next hEdge1 (next hEdge2 (next hEdge3 (next hEdge4 (next hEdge5 (next hEdge6 (next hEdge7 (next hEdge8 (next hEdge9 (next acknowledge-edge (next wait-edge (next e67 (next e68 (next e69 (next e70 (next e71 (next e72 (next e73 (next e74 (done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  finished : RR.owner (relays v74) ≡ RR.finished
  finished = refl
  quiescent : Quiescent (inner v74)
  quiescent = quiescence {c₀ = C.c₀} {g = C.settings} {start = C.initial} {scheduled = true} {as = actions} {final = inner v74} {t = just RR.joined} initializer progress-run
  physical-result : ready (base (inner v74)) A.child₀ ≡ true
  physical-result = refl
