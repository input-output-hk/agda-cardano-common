{-# OPTIONS --guardedness #-}

-- Reachable OG failure/backoff/retry path for the socket-open reservation leak.
-- The CM-level source replay is documented in SourceReplay/README.md.
module ConnectionManagement.CSP.GovernorOpenFailure where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; put; lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.CSP.OutboundAdmission as O
import ConnectionManagement.CSP.OutboundOpenFailure as E
import ConnectionManagement.CSP.GovernorLifecycle as L
open import ConnectionManagement.Subsystem
open import ConnectionManagement.CSP.Subsystem using (Process; trace-intro; Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

work : G.Job
work = G.job G.establish L.peerAddr nothing
completion₀ : G.Completion
completion₀ = G.completion work G.failed 2
failedState : G.State
failedState = G.complete 5 60 0 completion₀ L.g1
promotingAgain : G.State
promotingAgain = G.mark G.establish (L.peerAddr ∷ []) failedState
failedAgain : G.State
failedAgain = G.complete 5 60 5 completion₀ promotingAgain

frame₀ : J.PC → Bool → Bool → JobFrame
frame₀ pc queued deregistered = jobFrame
  (J.frame work L.caller L.child (ident 10) (ident 0) pc) queued deregistered
frame₁ : J.PC → Bool → Bool → JobFrame
frame₁ pc queued deregistered = jobFrame
  (J.frame work (ident 20) (ident 21) (ident 20) (ident 1) pc) queued deregistered
oldJobs : Store JobId JobFrame
oldJobs = (ident 0 , frame₀ (J.complete G.failed) true true) ∷ []
request₂ : A.Request
request₂ = A.acquireRequest L.peerAddr (ident 21) (ident 20) outbound nothing
retryAt : A.PC → ℕ → CM.Configuration
retryAt pc generation = record E.returned
  { acquiring = (ident 20 , A.frame request₂ pc) ∷ []; randomGeneration = generation }
retryReturned : CM.Configuration
retryReturned = record E.returned
  { acquired = put (ident 20) (C.raised C.connectionExists) (CM.acquired E.returned)
  ; randomGeneration = 2 }

c13 : Configuration
c13 = L.c13

a14 : Action
a14 = core (CM.acquire L.caller (A.failIO (errorId 1)))
c14 : Configuration
c14 = configuration (J.world (E.failed) []) (L.g1) (L.settings)
  (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , frame₀ J.awaitAcquire false false) ∷ []) (ident 0 ∷ []) ([]) [] 1 1 5 60 (nothing) false
step14 : advance a14 c13 ≡ just c14
step14 = refl

a15 : Action
a15 = core (CM.acquire L.caller A.returnResult)
c15 : Configuration
c15 = configuration (J.world (E.returned) []) (L.g1) (L.settings)
  (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , frame₀ J.awaitAcquire false false) ∷ []) (ident 0 ∷ []) ([]) [] 1 1 5 60 (nothing) false
step15 : advance a15 c14 ≡ just c15
step15 = refl

a16 : Action
a16 = jobStep (ident 0) J.collectAcquire
c16 : Configuration
c16 = configuration (J.world (E.returned) []) (L.g1) (L.settings)
  (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , frame₀ (J.acquirePolicy (C.ioFailure (errorId 1))) false false) ∷ []) (ident 0 ∷ []) ([]) [] 1 1 5 60 (nothing) false
step16 : advance a16 c15 ≡ just c16
step16 = refl

a17 : Action
a17 = jobStep (ident 0) J.choosePeerPolicy
c17 : Configuration
c17 = configuration (J.world (E.returned) []) (L.g1) (L.settings)
  (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , frame₀ (J.complete G.failed) false false) ∷ []) (ident 0 ∷ []) ([]) [] 1 1 5 60 (nothing) false
step17 : advance a17 c16 ≡ just c17
step17 = refl

a18 : Action
a18 = enqueueCompletion (ident 0) 2
c18 : Configuration
c18 = configuration (J.world (E.returned) []) (L.g1) (L.settings)
  (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , frame₀ (J.complete G.failed) true false) ∷ []) (ident 0 ∷ []) (completion₀ ∷ []) [] 1 1 5 60 (nothing) false
step18 : advance a18 c17 ≡ just c18
step18 = refl

a19 : Action
a19 = deregisterJob (ident 0)
c19 : Configuration
c19 = configuration (J.world (E.returned) []) (L.g1) (L.settings)
  (launch []) 0 (G.targets 1 1 1)
  (oldJobs) ([]) (completion₀ ∷ []) [] 1 1 5 60 (nothing) false
step19 : advance a19 c18 ≡ just c19
step19 = refl

a20 : Action
a20 = finishLaunch
c20 : Configuration
c20 = configuration (J.world (E.returned) []) (L.g1) (L.settings)
  (publishPublic) 0 (G.targets 1 1 1)
  (oldJobs) ([]) (completion₀ ∷ []) [] 1 1 5 60 (nothing) false
step20 : advance a20 c19 ≡ just c20
step20 = refl

a21 : Action
a21 = publishPublicState
c21 : Configuration
c21 = configuration (J.world (E.returned) []) (L.g1) (L.g1)
  (sampleInputs) 0 (G.targets 1 1 1)
  (oldJobs) ([]) (completion₀ ∷ []) [] 1 1 5 60 (nothing) false
step21 : advance a21 c20 ≡ just c21
step21 = refl

a22 : Action
a22 = sampleTime 0
c22 : Configuration
c22 = configuration (J.world (E.returned) []) (L.g1) (L.g1)
  (prepareWait) 0 (G.targets 1 1 1)
  (oldJobs) ([]) (completion₀ ∷ []) [] 1 1 5 60 (nothing) false
step22 : advance a22 c21 ≡ just c22
step22 = refl

a23 : Action
a23 = registerWakeup
c23 : Configuration
c23 = configuration (J.world (E.returned) []) (L.g1) (L.g1)
  (selecting) 0 (G.targets 1 1 1)
  (oldJobs) ([]) (completion₀ ∷ []) [] 1 1 5 60 (nothing) false
step23 : advance a23 c22 ≡ just c23
step23 = refl

a24 : Action
a24 = selectCompletion
c24 : Configuration
c24 = configuration (J.world (E.returned) []) (L.g1) (L.g1)
  (apply (completion completion₀)) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step24 : advance a24 c23 ≡ just c24
step24 = refl

a25 : Action
a25 = applyAt 0
c25 : Configuration
c25 = configuration (J.world (E.returned) []) (failedState) (L.g1)
  (publishView []) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step25 : advance a25 c24 ≡ just c25
step25 = refl

a26 : Action
a26 = publishCounters
c26 : Configuration
c26 = configuration (J.world (E.returned) []) (failedState) (L.g1)
  (traceDecision []) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step26 : advance a26 c25 ≡ just c26
step26 = refl

a27 : Action
a27 = traceSelection
c27 : Configuration
c27 = configuration (J.world (E.returned) []) (failedState) (L.g1)
  (launch []) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step27 : advance a27 c26 ≡ just c27
step27 = refl

a28 : Action
a28 = finishLaunch
c28 : Configuration
c28 = configuration (J.world (E.returned) []) (failedState) (L.g1)
  (publishPublic) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step28 : advance a28 c27 ≡ just c28
step28 = refl

a29 : Action
a29 = publishPublicState
c29 : Configuration
c29 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (sampleInputs) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step29 : advance a29 c28 ≡ just c29
step29 = refl

a30 : Action
a30 = sampleTime 0
c30 : Configuration
c30 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (prepareWait) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step30 : advance a30 c29 ≡ just c30
step30 = refl

a31 : Action
a31 = registerWakeup
c31 : Configuration
c31 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (selecting) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (just 5) false
step31 : advance a31 c30 ≡ just c31
step31 = refl

a32 : Action
a32 = expireWakeup
c32 : Configuration
c32 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (selecting) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (just 5) true
step32 : advance a32 c31 ≡ just c32
step32 = refl

a33 : Action
a33 = selectWakeup
c33 : Configuration
c33 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (cancelTimer (wakeup 5)) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (just 5) true
step33 : advance a33 c32 ≡ just c33
step33 = refl

a34 : Action
a34 = cancelWakeup
c34 : Configuration
c34 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (apply (wakeup 5)) 0 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step34 : advance a34 c33 ≡ just c34
step34 = refl

a35 : Action
a35 = applyAt 5
c35 : Configuration
c35 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (publishView []) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step35 : advance a35 c34 ≡ just c35
step35 = refl

a36 : Action
a36 = publishCounters
c36 : Configuration
c36 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (traceDecision []) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step36 : advance a36 c35 ≡ just c36
step36 = refl

a37 : Action
a37 = traceSelection
c37 : Configuration
c37 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step37 : advance a37 c36 ≡ just c37
step37 = refl

a38 : Action
a38 = finishLaunch
c38 : Configuration
c38 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (publishPublic) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step38 : advance a38 c37 ≡ just c38
step38 = refl

a39 : Action
a39 = publishPublicState
c39 : Configuration
c39 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (sampleInputs) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step39 : advance a39 c38 ≡ just c39
step39 = refl

a40 : Action
a40 = sampleTime 5
c40 : Configuration
c40 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (prepareWait) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step40 : advance a40 c39 ≡ just c40
step40 = refl

a41 : Action
a41 = registerWakeup
c41 : Configuration
c41 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (selecting) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step41 : advance a41 c40 ≡ just c41
step41 = refl

a42 : Action
a42 = selectPolicy (L.peerAddr ∷ [])
c42 : Configuration
c42 = configuration (J.world (E.returned) []) (failedState) (failedState)
  (apply (policy (G.decision promotingAgain (work ∷ [])))) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step42 : advance a42 c41 ≡ just c42
step42 = refl

a43 : Action
a43 = applyAt 5
c43 : Configuration
c43 = configuration (J.world (E.returned) []) (promotingAgain) (failedState)
  (publishView (work ∷ [])) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step43 : advance a43 c42 ≡ just c43
step43 = refl

a44 : Action
a44 = publishCounters
c44 : Configuration
c44 = configuration (J.world (E.returned) []) (promotingAgain) (failedState)
  (traceDecision (work ∷ [])) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step44 : advance a44 c43 ≡ just c44
step44 = refl

a45 : Action
a45 = traceSelection
c45 : Configuration
c45 = configuration (J.world (E.returned) []) (promotingAgain) (failedState)
  (launch (work ∷ [])) 5 (G.targets 1 1 1)
  (oldJobs) ([]) ([]) [] 1 1 5 60 (nothing) false
step45 : advance a45 c44 ≡ just c45
step45 = refl

a46 : Action
a46 = forkJob (ident 20) (ident 21) (ident 20)
c46 : Configuration
c46 = configuration (J.world (E.returned) []) (promotingAgain) (failedState)
  (register (ident 1) []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.begin) false false) oldJobs) ([]) ([]) [] 2 2 5 60 (nothing) false
step46 : advance a46 c45 ≡ just c46
step46 = refl

a47 : Action
a47 = registerJob
c47 : Configuration
c47 = configuration (J.world (E.returned) []) (promotingAgain) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.begin) false false) oldJobs) (ident 1 ∷ []) ([]) [] 2 2 5 60 (nothing) false
step47 : advance a47 c46 ≡ just c47
step47 = refl

a48 : Action
a48 = jobStep (ident 1) J.enter
c48 : Configuration
c48 = configuration (J.world (retryAt A.selecting 1) []) (promotingAgain) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.awaitAcquire) false false) oldJobs) (ident 1 ∷ []) ([]) [] 2 2 5 60 (nothing) false
step48 : advance a48 c47 ≡ just c48
step48 = refl

a49 : Action
a49 = core (CM.acquire (ident 20) (A.select (just (ident 0))))
c49 : Configuration
c49 = configuration (J.world (retryAt (A.count (A.complete (C.raised C.connectionExists))) 2) []) (promotingAgain) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.awaitAcquire) false false) oldJobs) (ident 1 ∷ []) ([]) [] 2 2 5 60 (nothing) false
step49 : advance a49 c48 ≡ just c49
step49 = refl

a50 : Action
a50 = core (CM.acquire (ident 20) A.readCounters)
c50 : Configuration
c50 = configuration (J.world (retryAt (A.complete (C.raised C.connectionExists)) 2) []) (promotingAgain) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.awaitAcquire) false false) oldJobs) (ident 1 ∷ []) ([]) [] 2 2 5 60 (nothing) false
step50 : advance a50 c49 ≡ just c50
step50 = refl

a51 : Action
a51 = core (CM.acquire (ident 20) A.returnResult)
c51 : Configuration
c51 = configuration (J.world (retryReturned) []) (promotingAgain) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.awaitAcquire) false false) oldJobs) (ident 1 ∷ []) ([]) [] 2 2 5 60 (nothing) false
step51 : advance a51 c50 ≡ just c51
step51 = refl

a52 : Action
a52 = jobStep (ident 1) J.collectAcquire
c52 : Configuration
c52 = configuration (J.world (retryReturned) []) (promotingAgain) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.acquirePolicy C.connectionExists) false false) oldJobs) (ident 1 ∷ []) ([]) [] 2 2 5 60 (nothing) false
step52 : advance a52 c51 ≡ just c52
step52 = refl

a53 : Action
a53 = jobStep (ident 1) J.choosePeerPolicy
c53 : Configuration
c53 = configuration (J.world (retryReturned) []) (promotingAgain) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) false false) oldJobs) (ident 1 ∷ []) ([]) [] 2 2 5 60 (nothing) false
step53 : advance a53 c52 ≡ just c53
step53 = refl

a54 : Action
a54 = enqueueCompletion (ident 1) 2
c54 : Configuration
c54 = configuration (J.world (retryReturned) []) (promotingAgain) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true false) oldJobs) (ident 1 ∷ []) (completion₀ ∷ []) [] 2 2 5 60 (nothing) false
step54 : advance a54 c53 ≡ just c54
step54 = refl

a55 : Action
a55 = deregisterJob (ident 1)
c55 : Configuration
c55 = configuration (J.world (retryReturned) []) (promotingAgain) (failedState)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) (completion₀ ∷ []) [] 2 2 5 60 (nothing) false
step55 : advance a55 c54 ≡ just c55
step55 = refl

a56 : Action
a56 = finishLaunch
c56 : Configuration
c56 = configuration (J.world (retryReturned) []) (promotingAgain) (failedState)
  (publishPublic) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) (completion₀ ∷ []) [] 2 2 5 60 (nothing) false
step56 : advance a56 c55 ≡ just c56
step56 = refl

a57 : Action
a57 = publishPublicState
c57 : Configuration
c57 = configuration (J.world (retryReturned) []) (promotingAgain) (promotingAgain)
  (sampleInputs) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) (completion₀ ∷ []) [] 2 2 5 60 (nothing) false
step57 : advance a57 c56 ≡ just c57
step57 = refl

a58 : Action
a58 = sampleTime 5
c58 : Configuration
c58 = configuration (J.world (retryReturned) []) (promotingAgain) (promotingAgain)
  (prepareWait) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) (completion₀ ∷ []) [] 2 2 5 60 (nothing) false
step58 : advance a58 c57 ≡ just c58
step58 = refl

a59 : Action
a59 = registerWakeup
c59 : Configuration
c59 = configuration (J.world (retryReturned) []) (promotingAgain) (promotingAgain)
  (selecting) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) (completion₀ ∷ []) [] 2 2 5 60 (nothing) false
step59 : advance a59 c58 ≡ just c59
step59 = refl

a60 : Action
a60 = selectCompletion
c60 : Configuration
c60 = configuration (J.world (retryReturned) []) (promotingAgain) (promotingAgain)
  (apply (completion completion₀)) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) ([]) [] 2 2 5 60 (nothing) false
step60 : advance a60 c59 ≡ just c60
step60 = refl

a61 : Action
a61 = applyAt 5
c61 : Configuration
c61 = configuration (J.world (retryReturned) []) (failedAgain) (promotingAgain)
  (publishView []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) ([]) [] 2 2 5 60 (nothing) false
step61 : advance a61 c60 ≡ just c61
step61 = refl

a62 : Action
a62 = publishCounters
c62 : Configuration
c62 = configuration (J.world (retryReturned) []) (failedAgain) (promotingAgain)
  (traceDecision []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) ([]) [] 2 2 5 60 (nothing) false
step62 : advance a62 c61 ≡ just c62
step62 = refl

a63 : Action
a63 = traceSelection
c63 : Configuration
c63 = configuration (J.world (retryReturned) []) (failedAgain) (promotingAgain)
  (launch []) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) ([]) [] 2 2 5 60 (nothing) false
step63 : advance a63 c62 ≡ just c63
step63 = refl

a64 : Action
a64 = finishLaunch
c64 : Configuration
c64 = configuration (J.world (retryReturned) []) (failedAgain) (promotingAgain)
  (publishPublic) 5 (G.targets 1 1 1)
  (put (ident 1) (frame₁ (J.complete G.failed) true true) oldJobs) ([]) ([]) [] 2 2 5 60 (nothing) false
step64 : advance a64 c63 ≡ just c64
step64 = refl

schedule : List Action
schedule = L.a1 ∷ L.a2 ∷ L.a3 ∷ L.a4 ∷ L.a5 ∷ L.a6 ∷ L.a7 ∷ L.a8 ∷ L.a9 ∷ L.a10 ∷ L.a11 ∷ L.a12 ∷ L.a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ a19 ∷ a20 ∷ a21 ∷ a22 ∷ a23 ∷ a24 ∷ a25 ∷ a26 ∷ a27 ∷ a28 ∷ a29 ∷ a30 ∷ a31 ∷ a32 ∷ a33 ∷ a34 ∷ a35 ∷ a36 ∷ a37 ∷ a38 ∷ a39 ∷ a40 ∷ a41 ∷ a42 ∷ a43 ∷ a44 ∷ a45 ∷ a46 ∷ a47 ∷ a48 ∷ a49 ∷ a50 ∷ a51 ∷ a52 ∷ a53 ∷ a54 ∷ a55 ∷ a56 ∷ a57 ∷ a58 ∷ a59 ∷ a60 ∷ a61 ∷ a62 ∷ a63 ∷ a64 ∷ []
path : Executes L.c₀ schedule c64
path = next {c₁ = L.c1} refl (next {c₁ = L.c2} refl (next {c₁ = L.c3} refl (next {c₁ = L.c4} refl (next {c₁ = L.c5} refl (next {c₁ = L.c6} refl (next {c₁ = L.c7} refl (next {c₁ = L.c8} refl (next {c₁ = L.c9} refl (next {c₁ = L.c10} refl (next {c₁ = L.c11} refl (next {c₁ = L.c12} refl (next {c₁ = L.c13} refl (next {c₁ = c14} refl (next {c₁ = c15} refl (next {c₁ = c16} refl (next {c₁ = c17} refl (next {c₁ = c18} refl (next {c₁ = c19} refl (next {c₁ = c20} refl (next {c₁ = c21} refl (next {c₁ = c22} refl (next {c₁ = c23} refl (next {c₁ = c24} refl (next {c₁ = c25} refl (next {c₁ = c26} refl (next {c₁ = c27} refl (next {c₁ = c28} refl (next {c₁ = c29} refl (next {c₁ = c30} refl (next {c₁ = c31} refl (next {c₁ = c32} refl (next {c₁ = c33} refl (next {c₁ = c34} refl (next {c₁ = c35} refl (next {c₁ = c36} refl (next {c₁ = c37} refl (next {c₁ = c38} refl (next {c₁ = c39} refl (next {c₁ = c40} refl (next {c₁ = c41} refl (next {c₁ = c42} refl (next {c₁ = c43} refl (next {c₁ = c44} refl (next {c₁ = c45} refl (next {c₁ = c46} refl (next {c₁ = c47} refl (next {c₁ = c48} refl (next {c₁ = c49} refl (next {c₁ = c50} refl (next {c₁ = c51} refl (next {c₁ = c52} refl (next {c₁ = c53} refl (next {c₁ = c54} refl (next {c₁ = c55} refl (next {c₁ = c56} refl (next {c₁ = c57} refl (next {c₁ = c58} refl (next {c₁ = c59} refl (next {c₁ = c60} refl (next {c₁ = c61} refl (next {c₁ = c62} refl (next {c₁ = c63} refl (next refl done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
accepted : traces (Process L.c₀) (map label schedule)
accepted = trace-intro path
step-count : length schedule ≡ 64
step-count = refl
