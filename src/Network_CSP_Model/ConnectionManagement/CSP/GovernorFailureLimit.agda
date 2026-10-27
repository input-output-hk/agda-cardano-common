{-# OPTIONS --guardedness #-}

-- Six failures with maxRetries = 5: ordinary OG forgets the peer, while the
-- captured CM reservation survives. No concurrent admission/discovery occurs.
module ConnectionManagement.CSP.GovernorFailureLimit where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; put)
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.CSP.GovernorOpenFailure as R
open import ConnectionManagement.Subsystem
open import ConnectionManagement.CSP.Subsystem using (Process; trace-intro; Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- Append certificates without re-evaluating the earlier failure/retry prefix.
append : ∀ {c c₁ c₂ as bs} → Executes c as c₁ → Executes c₁ bs c₂ → Executes c (as ++ bs) c₂
append done right = right
append (next eq left) right = next eq (append left right)

-- Each round uses fresh job, caller, child, socket and peer-handle identities.
jobAt : ℕ → ℕ → ℕ → J.PC → Bool → Bool → JobFrame
jobAt callerId childId peerId pc queued deregistered = jobFrame
  (J.frame R.work (ident callerId) (ident childId) (ident callerId) (ident peerId) pc) queued deregistered
requestAt : ℕ → ℕ → A.Request
requestAt callerId childId = A.acquireRequest L.peerAddr (ident childId) (ident callerId) outbound nothing
acquiringAt : CM.Configuration → ℕ → ℕ → ℕ → A.PC → CM.Configuration
acquiringAt priorCM callerId childId generation pc = record priorCM
  { acquiring = (ident callerId , A.frame (requestAt callerId childId) pc) ∷ []
  ; randomGeneration = generation }
returnedAt : CM.Configuration → ℕ → ℕ → CM.Configuration
returnedAt priorCM callerId generation = record priorCM
  { acquired = put (ident callerId) (C.raised C.connectionExists) (CM.acquired priorCM)
  ; randomGeneration = generation }

-- Snapshots hold expected fields, not results of executing advance. Every edge
-- is checked below, including the two clock samples around each wakeup.
snapshot : CM.Configuration → G.State → G.State → PC → ℕ →
  Store JobId JobFrame → List JobId → List G.Completion → ℕ → Maybe ℕ → Bool → Configuration
snapshot cm privateStateValue publicStateValue pc time jobs pool queue supply deadlineValue ready =
  configuration (J.world cm []) privateStateValue publicStateValue pc time (G.targets 1 1 1)
    jobs pool queue [] supply supply 5 60 deadlineValue ready

c64 : Configuration
c64 = R.c64
jobs2 : Store JobId JobFrame
jobs2 = jobs R.c64
cm2 : CM.Configuration
cm2 = R.retryReturned
g2 : G.State
g2 = R.failedAgain

-- Attempt 3, after 2 failures; due at model time 15.
promoting3 : G.State
promoting3 = G.mark G.establish (L.peerAddr ∷ []) g2
g3 : G.State
g3 = G.complete 5 60 15 R.completion₀ promoting3
cm3 : CM.Configuration
cm3 = returnedAt cm2 30 3
jobs3 : Store JobId JobFrame
jobs3 = put (ident 2) (jobAt 30 31 2 (J.complete G.failed) true true) jobs2

a65 : Action
a65 = publishPublicState
c65 : Configuration
c65 = snapshot (cm2) (g2) (g2) (sampleInputs) 5
  (jobs2) ([]) ([]) 2 (nothing) false

a66 : Action
a66 = sampleTime 5
c66 : Configuration
c66 = snapshot (cm2) (g2) (g2) (prepareWait) 5
  (jobs2) ([]) ([]) 2 (nothing) false

a67 : Action
a67 = registerWakeup
c67 : Configuration
c67 = snapshot (cm2) (g2) (g2) (selecting) 5
  (jobs2) ([]) ([]) 2 (just 15) false

a68 : Action
a68 = expireWakeup
c68 : Configuration
c68 = snapshot (cm2) (g2) (g2) (selecting) 5
  (jobs2) ([]) ([]) 2 (just 15) true

a69 : Action
a69 = selectWakeup
c69 : Configuration
c69 = snapshot (cm2) (g2) (g2) (cancelTimer (wakeup 15)) 5
  (jobs2) ([]) ([]) 2 (just 15) true

a70 : Action
a70 = cancelWakeup
c70 : Configuration
c70 = snapshot (cm2) (g2) (g2) (apply (wakeup 15)) 5
  (jobs2) ([]) ([]) 2 (nothing) false

a71 : Action
a71 = applyAt 15
c71 : Configuration
c71 = snapshot (cm2) (g2) (g2) (publishView []) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a72 : Action
a72 = publishCounters
c72 : Configuration
c72 = snapshot (cm2) (g2) (g2) (traceDecision []) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a73 : Action
a73 = traceSelection
c73 : Configuration
c73 = snapshot (cm2) (g2) (g2) (launch []) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a74 : Action
a74 = finishLaunch
c74 : Configuration
c74 = snapshot (cm2) (g2) (g2) (publishPublic) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a75 : Action
a75 = publishPublicState
c75 : Configuration
c75 = snapshot (cm2) (g2) (g2) (sampleInputs) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a76 : Action
a76 = sampleTime 15
c76 : Configuration
c76 = snapshot (cm2) (g2) (g2) (prepareWait) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a77 : Action
a77 = registerWakeup
c77 : Configuration
c77 = snapshot (cm2) (g2) (g2) (selecting) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a78 : Action
a78 = selectPolicy (L.peerAddr ∷ [])
c78 : Configuration
c78 = snapshot (cm2) (g2) (g2) (apply (policy (G.decision promoting3 (R.work ∷ [])))) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a79 : Action
a79 = applyAt 15
c79 : Configuration
c79 = snapshot (cm2) (promoting3) (g2) (publishView (R.work ∷ [])) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a80 : Action
a80 = publishCounters
c80 : Configuration
c80 = snapshot (cm2) (promoting3) (g2) (traceDecision (R.work ∷ [])) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a81 : Action
a81 = traceSelection
c81 : Configuration
c81 = snapshot (cm2) (promoting3) (g2) (launch (R.work ∷ [])) 15
  (jobs2) ([]) ([]) 2 (nothing) false

a82 : Action
a82 = forkJob (ident 30) (ident 31) (ident 30)
c82 : Configuration
c82 = snapshot (cm2) (promoting3) (g2) (register (ident 2) []) 15
  (put (ident 2) (jobAt 30 31 2 (J.begin) false false) jobs2) ([]) ([]) 3 (nothing) false

a83 : Action
a83 = registerJob
c83 : Configuration
c83 = snapshot (cm2) (promoting3) (g2) (launch []) 15
  (put (ident 2) (jobAt 30 31 2 (J.begin) false false) jobs2) (ident 2 ∷ []) ([]) 3 (nothing) false

a84 : Action
a84 = jobStep (ident 2) J.enter
c84 : Configuration
c84 = snapshot (acquiringAt cm2 30 31 2 A.selecting) (promoting3) (g2) (launch []) 15
  (put (ident 2) (jobAt 30 31 2 (J.awaitAcquire) false false) jobs2) (ident 2 ∷ []) ([]) 3 (nothing) false

a85 : Action
a85 = core (CM.acquire (ident 30) (A.select (just (ident 0))))
c85 : Configuration
c85 = snapshot (acquiringAt cm2 30 31 3 (A.count (A.complete (C.raised C.connectionExists)))) (promoting3) (g2) (launch []) 15
  (put (ident 2) (jobAt 30 31 2 (J.awaitAcquire) false false) jobs2) (ident 2 ∷ []) ([]) 3 (nothing) false

a86 : Action
a86 = core (CM.acquire (ident 30) A.readCounters)
c86 : Configuration
c86 = snapshot (acquiringAt cm2 30 31 3 (A.complete (C.raised C.connectionExists))) (promoting3) (g2) (launch []) 15
  (put (ident 2) (jobAt 30 31 2 (J.awaitAcquire) false false) jobs2) (ident 2 ∷ []) ([]) 3 (nothing) false

a87 : Action
a87 = core (CM.acquire (ident 30) A.returnResult)
c87 : Configuration
c87 = snapshot (cm3) (promoting3) (g2) (launch []) 15
  (put (ident 2) (jobAt 30 31 2 (J.awaitAcquire) false false) jobs2) (ident 2 ∷ []) ([]) 3 (nothing) false

a88 : Action
a88 = jobStep (ident 2) J.collectAcquire
c88 : Configuration
c88 = snapshot (cm3) (promoting3) (g2) (launch []) 15
  (put (ident 2) (jobAt 30 31 2 (J.acquirePolicy C.connectionExists) false false) jobs2) (ident 2 ∷ []) ([]) 3 (nothing) false

a89 : Action
a89 = jobStep (ident 2) J.choosePeerPolicy
c89 : Configuration
c89 = snapshot (cm3) (promoting3) (g2) (launch []) 15
  (put (ident 2) (jobAt 30 31 2 (J.complete G.failed) false false) jobs2) (ident 2 ∷ []) ([]) 3 (nothing) false

a90 : Action
a90 = enqueueCompletion (ident 2) 2
c90 : Configuration
c90 = snapshot (cm3) (promoting3) (g2) (launch []) 15
  (put (ident 2) (jobAt 30 31 2 (J.complete G.failed) true false) jobs2) (ident 2 ∷ []) (R.completion₀ ∷ []) 3 (nothing) false

a91 : Action
a91 = deregisterJob (ident 2)
c91 : Configuration
c91 = snapshot (cm3) (promoting3) (g2) (launch []) 15
  (jobs3) ([]) (R.completion₀ ∷ []) 3 (nothing) false

a92 : Action
a92 = finishLaunch
c92 : Configuration
c92 = snapshot (cm3) (promoting3) (g2) (publishPublic) 15
  (jobs3) ([]) (R.completion₀ ∷ []) 3 (nothing) false

a93 : Action
a93 = publishPublicState
c93 : Configuration
c93 = snapshot (cm3) (promoting3) (promoting3) (sampleInputs) 15
  (jobs3) ([]) (R.completion₀ ∷ []) 3 (nothing) false

a94 : Action
a94 = sampleTime 15
c94 : Configuration
c94 = snapshot (cm3) (promoting3) (promoting3) (prepareWait) 15
  (jobs3) ([]) (R.completion₀ ∷ []) 3 (nothing) false

a95 : Action
a95 = registerWakeup
c95 : Configuration
c95 = snapshot (cm3) (promoting3) (promoting3) (selecting) 15
  (jobs3) ([]) (R.completion₀ ∷ []) 3 (nothing) false

a96 : Action
a96 = selectCompletion
c96 : Configuration
c96 = snapshot (cm3) (promoting3) (promoting3) (apply (completion R.completion₀)) 15
  (jobs3) ([]) ([]) 3 (nothing) false

a97 : Action
a97 = applyAt 15
c97 : Configuration
c97 = snapshot (cm3) (g3) (promoting3) (publishView []) 15
  (jobs3) ([]) ([]) 3 (nothing) false

a98 : Action
a98 = publishCounters
c98 : Configuration
c98 = snapshot (cm3) (g3) (promoting3) (traceDecision []) 15
  (jobs3) ([]) ([]) 3 (nothing) false

a99 : Action
a99 = traceSelection
c99 : Configuration
c99 = snapshot (cm3) (g3) (promoting3) (launch []) 15
  (jobs3) ([]) ([]) 3 (nothing) false

a100 : Action
a100 = finishLaunch
c100 : Configuration
c100 = snapshot (cm3) (g3) (promoting3) (publishPublic) 15
  (jobs3) ([]) ([]) 3 (nothing) false

round3 : List Action
round3 = a65 ∷ a66 ∷ a67 ∷ a68 ∷ a69 ∷ a70 ∷ a71 ∷ a72 ∷ a73 ∷ a74 ∷ a75 ∷ a76 ∷ a77 ∷ a78 ∷ a79 ∷ a80 ∷ a81 ∷ a82 ∷ a83 ∷ a84 ∷ a85 ∷ a86 ∷ a87 ∷ a88 ∷ a89 ∷ a90 ∷ a91 ∷ a92 ∷ a93 ∷ a94 ∷ a95 ∷ a96 ∷ a97 ∷ a98 ∷ a99 ∷ a100 ∷ []
path3 : Executes c64 round3 c100
path3 = next {c₁ = c65} refl (next {c₁ = c66} refl (next {c₁ = c67} refl (next {c₁ = c68} refl (next {c₁ = c69} refl (next {c₁ = c70} refl (next {c₁ = c71} refl (next {c₁ = c72} refl (next {c₁ = c73} refl (next {c₁ = c74} refl (next {c₁ = c75} refl (next {c₁ = c76} refl (next {c₁ = c77} refl (next {c₁ = c78} refl (next {c₁ = c79} refl (next {c₁ = c80} refl (next {c₁ = c81} refl (next {c₁ = c82} refl (next {c₁ = c83} refl (next {c₁ = c84} refl (next {c₁ = c85} refl (next {c₁ = c86} refl (next {c₁ = c87} refl (next {c₁ = c88} refl (next {c₁ = c89} refl (next {c₁ = c90} refl (next {c₁ = c91} refl (next {c₁ = c92} refl (next {c₁ = c93} refl (next {c₁ = c94} refl (next {c₁ = c95} refl (next {c₁ = c96} refl (next {c₁ = c97} refl (next {c₁ = c98} refl (next {c₁ = c99} refl (next refl done)))))))))))))))))))))))))))))))))))

-- Attempt 4, after 3 failures; due at model time 35.
promoting4 : G.State
promoting4 = G.mark G.establish (L.peerAddr ∷ []) g3
g4 : G.State
g4 = G.complete 5 60 35 R.completion₀ promoting4
cm4 : CM.Configuration
cm4 = returnedAt cm3 40 4
jobs4 : Store JobId JobFrame
jobs4 = put (ident 3) (jobAt 40 41 3 (J.complete G.failed) true true) jobs3

a101 : Action
a101 = publishPublicState
c101 : Configuration
c101 = snapshot (cm3) (g3) (g3) (sampleInputs) 15
  (jobs3) ([]) ([]) 3 (nothing) false

a102 : Action
a102 = sampleTime 15
c102 : Configuration
c102 = snapshot (cm3) (g3) (g3) (prepareWait) 15
  (jobs3) ([]) ([]) 3 (nothing) false

a103 : Action
a103 = registerWakeup
c103 : Configuration
c103 = snapshot (cm3) (g3) (g3) (selecting) 15
  (jobs3) ([]) ([]) 3 (just 35) false

a104 : Action
a104 = expireWakeup
c104 : Configuration
c104 = snapshot (cm3) (g3) (g3) (selecting) 15
  (jobs3) ([]) ([]) 3 (just 35) true

a105 : Action
a105 = selectWakeup
c105 : Configuration
c105 = snapshot (cm3) (g3) (g3) (cancelTimer (wakeup 35)) 15
  (jobs3) ([]) ([]) 3 (just 35) true

a106 : Action
a106 = cancelWakeup
c106 : Configuration
c106 = snapshot (cm3) (g3) (g3) (apply (wakeup 35)) 15
  (jobs3) ([]) ([]) 3 (nothing) false

a107 : Action
a107 = applyAt 35
c107 : Configuration
c107 = snapshot (cm3) (g3) (g3) (publishView []) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a108 : Action
a108 = publishCounters
c108 : Configuration
c108 = snapshot (cm3) (g3) (g3) (traceDecision []) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a109 : Action
a109 = traceSelection
c109 : Configuration
c109 = snapshot (cm3) (g3) (g3) (launch []) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a110 : Action
a110 = finishLaunch
c110 : Configuration
c110 = snapshot (cm3) (g3) (g3) (publishPublic) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a111 : Action
a111 = publishPublicState
c111 : Configuration
c111 = snapshot (cm3) (g3) (g3) (sampleInputs) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a112 : Action
a112 = sampleTime 35
c112 : Configuration
c112 = snapshot (cm3) (g3) (g3) (prepareWait) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a113 : Action
a113 = registerWakeup
c113 : Configuration
c113 = snapshot (cm3) (g3) (g3) (selecting) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a114 : Action
a114 = selectPolicy (L.peerAddr ∷ [])
c114 : Configuration
c114 = snapshot (cm3) (g3) (g3) (apply (policy (G.decision promoting4 (R.work ∷ [])))) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a115 : Action
a115 = applyAt 35
c115 : Configuration
c115 = snapshot (cm3) (promoting4) (g3) (publishView (R.work ∷ [])) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a116 : Action
a116 = publishCounters
c116 : Configuration
c116 = snapshot (cm3) (promoting4) (g3) (traceDecision (R.work ∷ [])) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a117 : Action
a117 = traceSelection
c117 : Configuration
c117 = snapshot (cm3) (promoting4) (g3) (launch (R.work ∷ [])) 35
  (jobs3) ([]) ([]) 3 (nothing) false

a118 : Action
a118 = forkJob (ident 40) (ident 41) (ident 40)
c118 : Configuration
c118 = snapshot (cm3) (promoting4) (g3) (register (ident 3) []) 35
  (put (ident 3) (jobAt 40 41 3 (J.begin) false false) jobs3) ([]) ([]) 4 (nothing) false

a119 : Action
a119 = registerJob
c119 : Configuration
c119 = snapshot (cm3) (promoting4) (g3) (launch []) 35
  (put (ident 3) (jobAt 40 41 3 (J.begin) false false) jobs3) (ident 3 ∷ []) ([]) 4 (nothing) false

a120 : Action
a120 = jobStep (ident 3) J.enter
c120 : Configuration
c120 = snapshot (acquiringAt cm3 40 41 3 A.selecting) (promoting4) (g3) (launch []) 35
  (put (ident 3) (jobAt 40 41 3 (J.awaitAcquire) false false) jobs3) (ident 3 ∷ []) ([]) 4 (nothing) false

a121 : Action
a121 = core (CM.acquire (ident 40) (A.select (just (ident 0))))
c121 : Configuration
c121 = snapshot (acquiringAt cm3 40 41 4 (A.count (A.complete (C.raised C.connectionExists)))) (promoting4) (g3) (launch []) 35
  (put (ident 3) (jobAt 40 41 3 (J.awaitAcquire) false false) jobs3) (ident 3 ∷ []) ([]) 4 (nothing) false

a122 : Action
a122 = core (CM.acquire (ident 40) A.readCounters)
c122 : Configuration
c122 = snapshot (acquiringAt cm3 40 41 4 (A.complete (C.raised C.connectionExists))) (promoting4) (g3) (launch []) 35
  (put (ident 3) (jobAt 40 41 3 (J.awaitAcquire) false false) jobs3) (ident 3 ∷ []) ([]) 4 (nothing) false

a123 : Action
a123 = core (CM.acquire (ident 40) A.returnResult)
c123 : Configuration
c123 = snapshot (cm4) (promoting4) (g3) (launch []) 35
  (put (ident 3) (jobAt 40 41 3 (J.awaitAcquire) false false) jobs3) (ident 3 ∷ []) ([]) 4 (nothing) false

a124 : Action
a124 = jobStep (ident 3) J.collectAcquire
c124 : Configuration
c124 = snapshot (cm4) (promoting4) (g3) (launch []) 35
  (put (ident 3) (jobAt 40 41 3 (J.acquirePolicy C.connectionExists) false false) jobs3) (ident 3 ∷ []) ([]) 4 (nothing) false

a125 : Action
a125 = jobStep (ident 3) J.choosePeerPolicy
c125 : Configuration
c125 = snapshot (cm4) (promoting4) (g3) (launch []) 35
  (put (ident 3) (jobAt 40 41 3 (J.complete G.failed) false false) jobs3) (ident 3 ∷ []) ([]) 4 (nothing) false

a126 : Action
a126 = enqueueCompletion (ident 3) 2
c126 : Configuration
c126 = snapshot (cm4) (promoting4) (g3) (launch []) 35
  (put (ident 3) (jobAt 40 41 3 (J.complete G.failed) true false) jobs3) (ident 3 ∷ []) (R.completion₀ ∷ []) 4 (nothing) false

a127 : Action
a127 = deregisterJob (ident 3)
c127 : Configuration
c127 = snapshot (cm4) (promoting4) (g3) (launch []) 35
  (jobs4) ([]) (R.completion₀ ∷ []) 4 (nothing) false

a128 : Action
a128 = finishLaunch
c128 : Configuration
c128 = snapshot (cm4) (promoting4) (g3) (publishPublic) 35
  (jobs4) ([]) (R.completion₀ ∷ []) 4 (nothing) false

a129 : Action
a129 = publishPublicState
c129 : Configuration
c129 = snapshot (cm4) (promoting4) (promoting4) (sampleInputs) 35
  (jobs4) ([]) (R.completion₀ ∷ []) 4 (nothing) false

a130 : Action
a130 = sampleTime 35
c130 : Configuration
c130 = snapshot (cm4) (promoting4) (promoting4) (prepareWait) 35
  (jobs4) ([]) (R.completion₀ ∷ []) 4 (nothing) false

a131 : Action
a131 = registerWakeup
c131 : Configuration
c131 = snapshot (cm4) (promoting4) (promoting4) (selecting) 35
  (jobs4) ([]) (R.completion₀ ∷ []) 4 (nothing) false

a132 : Action
a132 = selectCompletion
c132 : Configuration
c132 = snapshot (cm4) (promoting4) (promoting4) (apply (completion R.completion₀)) 35
  (jobs4) ([]) ([]) 4 (nothing) false

a133 : Action
a133 = applyAt 35
c133 : Configuration
c133 = snapshot (cm4) (g4) (promoting4) (publishView []) 35
  (jobs4) ([]) ([]) 4 (nothing) false

a134 : Action
a134 = publishCounters
c134 : Configuration
c134 = snapshot (cm4) (g4) (promoting4) (traceDecision []) 35
  (jobs4) ([]) ([]) 4 (nothing) false

a135 : Action
a135 = traceSelection
c135 : Configuration
c135 = snapshot (cm4) (g4) (promoting4) (launch []) 35
  (jobs4) ([]) ([]) 4 (nothing) false

a136 : Action
a136 = finishLaunch
c136 : Configuration
c136 = snapshot (cm4) (g4) (promoting4) (publishPublic) 35
  (jobs4) ([]) ([]) 4 (nothing) false

round4 : List Action
round4 = a101 ∷ a102 ∷ a103 ∷ a104 ∷ a105 ∷ a106 ∷ a107 ∷ a108 ∷ a109 ∷ a110 ∷ a111 ∷ a112 ∷ a113 ∷ a114 ∷ a115 ∷ a116 ∷ a117 ∷ a118 ∷ a119 ∷ a120 ∷ a121 ∷ a122 ∷ a123 ∷ a124 ∷ a125 ∷ a126 ∷ a127 ∷ a128 ∷ a129 ∷ a130 ∷ a131 ∷ a132 ∷ a133 ∷ a134 ∷ a135 ∷ a136 ∷ []
path4 : Executes c100 round4 c136
path4 = next {c₁ = c101} refl (next {c₁ = c102} refl (next {c₁ = c103} refl (next {c₁ = c104} refl (next {c₁ = c105} refl (next {c₁ = c106} refl (next {c₁ = c107} refl (next {c₁ = c108} refl (next {c₁ = c109} refl (next {c₁ = c110} refl (next {c₁ = c111} refl (next {c₁ = c112} refl (next {c₁ = c113} refl (next {c₁ = c114} refl (next {c₁ = c115} refl (next {c₁ = c116} refl (next {c₁ = c117} refl (next {c₁ = c118} refl (next {c₁ = c119} refl (next {c₁ = c120} refl (next {c₁ = c121} refl (next {c₁ = c122} refl (next {c₁ = c123} refl (next {c₁ = c124} refl (next {c₁ = c125} refl (next {c₁ = c126} refl (next {c₁ = c127} refl (next {c₁ = c128} refl (next {c₁ = c129} refl (next {c₁ = c130} refl (next {c₁ = c131} refl (next {c₁ = c132} refl (next {c₁ = c133} refl (next {c₁ = c134} refl (next {c₁ = c135} refl (next refl done)))))))))))))))))))))))))))))))))))

-- Attempt 5, after 4 failures; due at model time 75.
promoting5 : G.State
promoting5 = G.mark G.establish (L.peerAddr ∷ []) g4
g5 : G.State
g5 = G.complete 5 60 75 R.completion₀ promoting5
cm5 : CM.Configuration
cm5 = returnedAt cm4 50 5
jobs5 : Store JobId JobFrame
jobs5 = put (ident 4) (jobAt 50 51 4 (J.complete G.failed) true true) jobs4

a137 : Action
a137 = publishPublicState
c137 : Configuration
c137 = snapshot (cm4) (g4) (g4) (sampleInputs) 35
  (jobs4) ([]) ([]) 4 (nothing) false

a138 : Action
a138 = sampleTime 35
c138 : Configuration
c138 = snapshot (cm4) (g4) (g4) (prepareWait) 35
  (jobs4) ([]) ([]) 4 (nothing) false

a139 : Action
a139 = registerWakeup
c139 : Configuration
c139 = snapshot (cm4) (g4) (g4) (selecting) 35
  (jobs4) ([]) ([]) 4 (just 75) false

a140 : Action
a140 = expireWakeup
c140 : Configuration
c140 = snapshot (cm4) (g4) (g4) (selecting) 35
  (jobs4) ([]) ([]) 4 (just 75) true

a141 : Action
a141 = selectWakeup
c141 : Configuration
c141 = snapshot (cm4) (g4) (g4) (cancelTimer (wakeup 75)) 35
  (jobs4) ([]) ([]) 4 (just 75) true

a142 : Action
a142 = cancelWakeup
c142 : Configuration
c142 = snapshot (cm4) (g4) (g4) (apply (wakeup 75)) 35
  (jobs4) ([]) ([]) 4 (nothing) false

a143 : Action
a143 = applyAt 75
c143 : Configuration
c143 = snapshot (cm4) (g4) (g4) (publishView []) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a144 : Action
a144 = publishCounters
c144 : Configuration
c144 = snapshot (cm4) (g4) (g4) (traceDecision []) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a145 : Action
a145 = traceSelection
c145 : Configuration
c145 = snapshot (cm4) (g4) (g4) (launch []) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a146 : Action
a146 = finishLaunch
c146 : Configuration
c146 = snapshot (cm4) (g4) (g4) (publishPublic) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a147 : Action
a147 = publishPublicState
c147 : Configuration
c147 = snapshot (cm4) (g4) (g4) (sampleInputs) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a148 : Action
a148 = sampleTime 75
c148 : Configuration
c148 = snapshot (cm4) (g4) (g4) (prepareWait) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a149 : Action
a149 = registerWakeup
c149 : Configuration
c149 = snapshot (cm4) (g4) (g4) (selecting) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a150 : Action
a150 = selectPolicy (L.peerAddr ∷ [])
c150 : Configuration
c150 = snapshot (cm4) (g4) (g4) (apply (policy (G.decision promoting5 (R.work ∷ [])))) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a151 : Action
a151 = applyAt 75
c151 : Configuration
c151 = snapshot (cm4) (promoting5) (g4) (publishView (R.work ∷ [])) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a152 : Action
a152 = publishCounters
c152 : Configuration
c152 = snapshot (cm4) (promoting5) (g4) (traceDecision (R.work ∷ [])) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a153 : Action
a153 = traceSelection
c153 : Configuration
c153 = snapshot (cm4) (promoting5) (g4) (launch (R.work ∷ [])) 75
  (jobs4) ([]) ([]) 4 (nothing) false

a154 : Action
a154 = forkJob (ident 50) (ident 51) (ident 50)
c154 : Configuration
c154 = snapshot (cm4) (promoting5) (g4) (register (ident 4) []) 75
  (put (ident 4) (jobAt 50 51 4 (J.begin) false false) jobs4) ([]) ([]) 5 (nothing) false

a155 : Action
a155 = registerJob
c155 : Configuration
c155 = snapshot (cm4) (promoting5) (g4) (launch []) 75
  (put (ident 4) (jobAt 50 51 4 (J.begin) false false) jobs4) (ident 4 ∷ []) ([]) 5 (nothing) false

a156 : Action
a156 = jobStep (ident 4) J.enter
c156 : Configuration
c156 = snapshot (acquiringAt cm4 50 51 4 A.selecting) (promoting5) (g4) (launch []) 75
  (put (ident 4) (jobAt 50 51 4 (J.awaitAcquire) false false) jobs4) (ident 4 ∷ []) ([]) 5 (nothing) false

a157 : Action
a157 = core (CM.acquire (ident 50) (A.select (just (ident 0))))
c157 : Configuration
c157 = snapshot (acquiringAt cm4 50 51 5 (A.count (A.complete (C.raised C.connectionExists)))) (promoting5) (g4) (launch []) 75
  (put (ident 4) (jobAt 50 51 4 (J.awaitAcquire) false false) jobs4) (ident 4 ∷ []) ([]) 5 (nothing) false

a158 : Action
a158 = core (CM.acquire (ident 50) A.readCounters)
c158 : Configuration
c158 = snapshot (acquiringAt cm4 50 51 5 (A.complete (C.raised C.connectionExists))) (promoting5) (g4) (launch []) 75
  (put (ident 4) (jobAt 50 51 4 (J.awaitAcquire) false false) jobs4) (ident 4 ∷ []) ([]) 5 (nothing) false

a159 : Action
a159 = core (CM.acquire (ident 50) A.returnResult)
c159 : Configuration
c159 = snapshot (cm5) (promoting5) (g4) (launch []) 75
  (put (ident 4) (jobAt 50 51 4 (J.awaitAcquire) false false) jobs4) (ident 4 ∷ []) ([]) 5 (nothing) false

a160 : Action
a160 = jobStep (ident 4) J.collectAcquire
c160 : Configuration
c160 = snapshot (cm5) (promoting5) (g4) (launch []) 75
  (put (ident 4) (jobAt 50 51 4 (J.acquirePolicy C.connectionExists) false false) jobs4) (ident 4 ∷ []) ([]) 5 (nothing) false

a161 : Action
a161 = jobStep (ident 4) J.choosePeerPolicy
c161 : Configuration
c161 = snapshot (cm5) (promoting5) (g4) (launch []) 75
  (put (ident 4) (jobAt 50 51 4 (J.complete G.failed) false false) jobs4) (ident 4 ∷ []) ([]) 5 (nothing) false

a162 : Action
a162 = enqueueCompletion (ident 4) 2
c162 : Configuration
c162 = snapshot (cm5) (promoting5) (g4) (launch []) 75
  (put (ident 4) (jobAt 50 51 4 (J.complete G.failed) true false) jobs4) (ident 4 ∷ []) (R.completion₀ ∷ []) 5 (nothing) false

a163 : Action
a163 = deregisterJob (ident 4)
c163 : Configuration
c163 = snapshot (cm5) (promoting5) (g4) (launch []) 75
  (jobs5) ([]) (R.completion₀ ∷ []) 5 (nothing) false

a164 : Action
a164 = finishLaunch
c164 : Configuration
c164 = snapshot (cm5) (promoting5) (g4) (publishPublic) 75
  (jobs5) ([]) (R.completion₀ ∷ []) 5 (nothing) false

a165 : Action
a165 = publishPublicState
c165 : Configuration
c165 = snapshot (cm5) (promoting5) (promoting5) (sampleInputs) 75
  (jobs5) ([]) (R.completion₀ ∷ []) 5 (nothing) false

a166 : Action
a166 = sampleTime 75
c166 : Configuration
c166 = snapshot (cm5) (promoting5) (promoting5) (prepareWait) 75
  (jobs5) ([]) (R.completion₀ ∷ []) 5 (nothing) false

a167 : Action
a167 = registerWakeup
c167 : Configuration
c167 = snapshot (cm5) (promoting5) (promoting5) (selecting) 75
  (jobs5) ([]) (R.completion₀ ∷ []) 5 (nothing) false

a168 : Action
a168 = selectCompletion
c168 : Configuration
c168 = snapshot (cm5) (promoting5) (promoting5) (apply (completion R.completion₀)) 75
  (jobs5) ([]) ([]) 5 (nothing) false

a169 : Action
a169 = applyAt 75
c169 : Configuration
c169 = snapshot (cm5) (g5) (promoting5) (publishView []) 75
  (jobs5) ([]) ([]) 5 (nothing) false

a170 : Action
a170 = publishCounters
c170 : Configuration
c170 = snapshot (cm5) (g5) (promoting5) (traceDecision []) 75
  (jobs5) ([]) ([]) 5 (nothing) false

a171 : Action
a171 = traceSelection
c171 : Configuration
c171 = snapshot (cm5) (g5) (promoting5) (launch []) 75
  (jobs5) ([]) ([]) 5 (nothing) false

a172 : Action
a172 = finishLaunch
c172 : Configuration
c172 = snapshot (cm5) (g5) (promoting5) (publishPublic) 75
  (jobs5) ([]) ([]) 5 (nothing) false

round5 : List Action
round5 = a137 ∷ a138 ∷ a139 ∷ a140 ∷ a141 ∷ a142 ∷ a143 ∷ a144 ∷ a145 ∷ a146 ∷ a147 ∷ a148 ∷ a149 ∷ a150 ∷ a151 ∷ a152 ∷ a153 ∷ a154 ∷ a155 ∷ a156 ∷ a157 ∷ a158 ∷ a159 ∷ a160 ∷ a161 ∷ a162 ∷ a163 ∷ a164 ∷ a165 ∷ a166 ∷ a167 ∷ a168 ∷ a169 ∷ a170 ∷ a171 ∷ a172 ∷ []
path5 : Executes c136 round5 c172
path5 = next {c₁ = c137} refl (next {c₁ = c138} refl (next {c₁ = c139} refl (next {c₁ = c140} refl (next {c₁ = c141} refl (next {c₁ = c142} refl (next {c₁ = c143} refl (next {c₁ = c144} refl (next {c₁ = c145} refl (next {c₁ = c146} refl (next {c₁ = c147} refl (next {c₁ = c148} refl (next {c₁ = c149} refl (next {c₁ = c150} refl (next {c₁ = c151} refl (next {c₁ = c152} refl (next {c₁ = c153} refl (next {c₁ = c154} refl (next {c₁ = c155} refl (next {c₁ = c156} refl (next {c₁ = c157} refl (next {c₁ = c158} refl (next {c₁ = c159} refl (next {c₁ = c160} refl (next {c₁ = c161} refl (next {c₁ = c162} refl (next {c₁ = c163} refl (next {c₁ = c164} refl (next {c₁ = c165} refl (next {c₁ = c166} refl (next {c₁ = c167} refl (next {c₁ = c168} refl (next {c₁ = c169} refl (next {c₁ = c170} refl (next {c₁ = c171} refl (next refl done)))))))))))))))))))))))))))))))))))

-- Attempt 6, after 5 failures; due at model time 155.
promoting6 : G.State
promoting6 = G.mark G.establish (L.peerAddr ∷ []) g5
g6 : G.State
g6 = G.complete 5 60 155 R.completion₀ promoting6
cm6 : CM.Configuration
cm6 = returnedAt cm5 60 6
jobs6 : Store JobId JobFrame
jobs6 = put (ident 5) (jobAt 60 61 5 (J.complete G.failed) true true) jobs5

a173 : Action
a173 = publishPublicState
c173 : Configuration
c173 = snapshot (cm5) (g5) (g5) (sampleInputs) 75
  (jobs5) ([]) ([]) 5 (nothing) false

a174 : Action
a174 = sampleTime 75
c174 : Configuration
c174 = snapshot (cm5) (g5) (g5) (prepareWait) 75
  (jobs5) ([]) ([]) 5 (nothing) false

a175 : Action
a175 = registerWakeup
c175 : Configuration
c175 = snapshot (cm5) (g5) (g5) (selecting) 75
  (jobs5) ([]) ([]) 5 (just 155) false

a176 : Action
a176 = expireWakeup
c176 : Configuration
c176 = snapshot (cm5) (g5) (g5) (selecting) 75
  (jobs5) ([]) ([]) 5 (just 155) true

a177 : Action
a177 = selectWakeup
c177 : Configuration
c177 = snapshot (cm5) (g5) (g5) (cancelTimer (wakeup 155)) 75
  (jobs5) ([]) ([]) 5 (just 155) true

a178 : Action
a178 = cancelWakeup
c178 : Configuration
c178 = snapshot (cm5) (g5) (g5) (apply (wakeup 155)) 75
  (jobs5) ([]) ([]) 5 (nothing) false

a179 : Action
a179 = applyAt 155
c179 : Configuration
c179 = snapshot (cm5) (g5) (g5) (publishView []) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a180 : Action
a180 = publishCounters
c180 : Configuration
c180 = snapshot (cm5) (g5) (g5) (traceDecision []) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a181 : Action
a181 = traceSelection
c181 : Configuration
c181 = snapshot (cm5) (g5) (g5) (launch []) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a182 : Action
a182 = finishLaunch
c182 : Configuration
c182 = snapshot (cm5) (g5) (g5) (publishPublic) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a183 : Action
a183 = publishPublicState
c183 : Configuration
c183 = snapshot (cm5) (g5) (g5) (sampleInputs) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a184 : Action
a184 = sampleTime 155
c184 : Configuration
c184 = snapshot (cm5) (g5) (g5) (prepareWait) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a185 : Action
a185 = registerWakeup
c185 : Configuration
c185 = snapshot (cm5) (g5) (g5) (selecting) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a186 : Action
a186 = selectPolicy (L.peerAddr ∷ [])
c186 : Configuration
c186 = snapshot (cm5) (g5) (g5) (apply (policy (G.decision promoting6 (R.work ∷ [])))) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a187 : Action
a187 = applyAt 155
c187 : Configuration
c187 = snapshot (cm5) (promoting6) (g5) (publishView (R.work ∷ [])) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a188 : Action
a188 = publishCounters
c188 : Configuration
c188 = snapshot (cm5) (promoting6) (g5) (traceDecision (R.work ∷ [])) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a189 : Action
a189 = traceSelection
c189 : Configuration
c189 = snapshot (cm5) (promoting6) (g5) (launch (R.work ∷ [])) 155
  (jobs5) ([]) ([]) 5 (nothing) false

a190 : Action
a190 = forkJob (ident 60) (ident 61) (ident 60)
c190 : Configuration
c190 = snapshot (cm5) (promoting6) (g5) (register (ident 5) []) 155
  (put (ident 5) (jobAt 60 61 5 (J.begin) false false) jobs5) ([]) ([]) 6 (nothing) false

a191 : Action
a191 = registerJob
c191 : Configuration
c191 = snapshot (cm5) (promoting6) (g5) (launch []) 155
  (put (ident 5) (jobAt 60 61 5 (J.begin) false false) jobs5) (ident 5 ∷ []) ([]) 6 (nothing) false

a192 : Action
a192 = jobStep (ident 5) J.enter
c192 : Configuration
c192 = snapshot (acquiringAt cm5 60 61 5 A.selecting) (promoting6) (g5) (launch []) 155
  (put (ident 5) (jobAt 60 61 5 (J.awaitAcquire) false false) jobs5) (ident 5 ∷ []) ([]) 6 (nothing) false

a193 : Action
a193 = core (CM.acquire (ident 60) (A.select (just (ident 0))))
c193 : Configuration
c193 = snapshot (acquiringAt cm5 60 61 6 (A.count (A.complete (C.raised C.connectionExists)))) (promoting6) (g5) (launch []) 155
  (put (ident 5) (jobAt 60 61 5 (J.awaitAcquire) false false) jobs5) (ident 5 ∷ []) ([]) 6 (nothing) false

a194 : Action
a194 = core (CM.acquire (ident 60) A.readCounters)
c194 : Configuration
c194 = snapshot (acquiringAt cm5 60 61 6 (A.complete (C.raised C.connectionExists))) (promoting6) (g5) (launch []) 155
  (put (ident 5) (jobAt 60 61 5 (J.awaitAcquire) false false) jobs5) (ident 5 ∷ []) ([]) 6 (nothing) false

a195 : Action
a195 = core (CM.acquire (ident 60) A.returnResult)
c195 : Configuration
c195 = snapshot (cm6) (promoting6) (g5) (launch []) 155
  (put (ident 5) (jobAt 60 61 5 (J.awaitAcquire) false false) jobs5) (ident 5 ∷ []) ([]) 6 (nothing) false

a196 : Action
a196 = jobStep (ident 5) J.collectAcquire
c196 : Configuration
c196 = snapshot (cm6) (promoting6) (g5) (launch []) 155
  (put (ident 5) (jobAt 60 61 5 (J.acquirePolicy C.connectionExists) false false) jobs5) (ident 5 ∷ []) ([]) 6 (nothing) false

a197 : Action
a197 = jobStep (ident 5) J.choosePeerPolicy
c197 : Configuration
c197 = snapshot (cm6) (promoting6) (g5) (launch []) 155
  (put (ident 5) (jobAt 60 61 5 (J.complete G.failed) false false) jobs5) (ident 5 ∷ []) ([]) 6 (nothing) false

a198 : Action
a198 = enqueueCompletion (ident 5) 2
c198 : Configuration
c198 = snapshot (cm6) (promoting6) (g5) (launch []) 155
  (put (ident 5) (jobAt 60 61 5 (J.complete G.failed) true false) jobs5) (ident 5 ∷ []) (R.completion₀ ∷ []) 6 (nothing) false

a199 : Action
a199 = deregisterJob (ident 5)
c199 : Configuration
c199 = snapshot (cm6) (promoting6) (g5) (launch []) 155
  (jobs6) ([]) (R.completion₀ ∷ []) 6 (nothing) false

a200 : Action
a200 = finishLaunch
c200 : Configuration
c200 = snapshot (cm6) (promoting6) (g5) (publishPublic) 155
  (jobs6) ([]) (R.completion₀ ∷ []) 6 (nothing) false

a201 : Action
a201 = publishPublicState
c201 : Configuration
c201 = snapshot (cm6) (promoting6) (promoting6) (sampleInputs) 155
  (jobs6) ([]) (R.completion₀ ∷ []) 6 (nothing) false

a202 : Action
a202 = sampleTime 155
c202 : Configuration
c202 = snapshot (cm6) (promoting6) (promoting6) (prepareWait) 155
  (jobs6) ([]) (R.completion₀ ∷ []) 6 (nothing) false

a203 : Action
a203 = registerWakeup
c203 : Configuration
c203 = snapshot (cm6) (promoting6) (promoting6) (selecting) 155
  (jobs6) ([]) (R.completion₀ ∷ []) 6 (nothing) false

a204 : Action
a204 = selectCompletion
c204 : Configuration
c204 = snapshot (cm6) (promoting6) (promoting6) (apply (completion R.completion₀)) 155
  (jobs6) ([]) ([]) 6 (nothing) false

a205 : Action
a205 = applyAt 155
c205 : Configuration
c205 = snapshot (cm6) (g6) (promoting6) (publishView []) 155
  (jobs6) ([]) ([]) 6 (nothing) false

a206 : Action
a206 = publishCounters
c206 : Configuration
c206 = snapshot (cm6) (g6) (promoting6) (traceDecision []) 155
  (jobs6) ([]) ([]) 6 (nothing) false

a207 : Action
a207 = traceSelection
c207 : Configuration
c207 = snapshot (cm6) (g6) (promoting6) (launch []) 155
  (jobs6) ([]) ([]) 6 (nothing) false

a208 : Action
a208 = finishLaunch
c208 : Configuration
c208 = snapshot (cm6) (g6) (promoting6) (publishPublic) 155
  (jobs6) ([]) ([]) 6 (nothing) false

round6 : List Action
round6 = a173 ∷ a174 ∷ a175 ∷ a176 ∷ a177 ∷ a178 ∷ a179 ∷ a180 ∷ a181 ∷ a182 ∷ a183 ∷ a184 ∷ a185 ∷ a186 ∷ a187 ∷ a188 ∷ a189 ∷ a190 ∷ a191 ∷ a192 ∷ a193 ∷ a194 ∷ a195 ∷ a196 ∷ a197 ∷ a198 ∷ a199 ∷ a200 ∷ a201 ∷ a202 ∷ a203 ∷ a204 ∷ a205 ∷ a206 ∷ a207 ∷ a208 ∷ []
path6 : Executes c172 round6 c208
path6 = next {c₁ = c173} refl (next {c₁ = c174} refl (next {c₁ = c175} refl (next {c₁ = c176} refl (next {c₁ = c177} refl (next {c₁ = c178} refl (next {c₁ = c179} refl (next {c₁ = c180} refl (next {c₁ = c181} refl (next {c₁ = c182} refl (next {c₁ = c183} refl (next {c₁ = c184} refl (next {c₁ = c185} refl (next {c₁ = c186} refl (next {c₁ = c187} refl (next {c₁ = c188} refl (next {c₁ = c189} refl (next {c₁ = c190} refl (next {c₁ = c191} refl (next {c₁ = c192} refl (next {c₁ = c193} refl (next {c₁ = c194} refl (next {c₁ = c195} refl (next {c₁ = c196} refl (next {c₁ = c197} refl (next {c₁ = c198} refl (next {c₁ = c199} refl (next {c₁ = c200} refl (next {c₁ = c201} refl (next {c₁ = c202} refl (next {c₁ = c203} refl (next {c₁ = c204} refl (next {c₁ = c205} refl (next {c₁ = c206} refl (next {c₁ = c207} refl (next refl done)))))))))))))))))))))))))))))))))))

a209 : Action
a209 = publishPublicState
c209 : Configuration
c209 = snapshot (cm6) (g6) (g6) (sampleInputs) 155
  (jobs6) ([]) ([]) 6 (nothing) false

a210 : Action
a210 = sampleTime 155
c210 : Configuration
c210 = snapshot (cm6) (g6) (g6) (prepareWait) 155
  (jobs6) ([]) ([]) 6 (nothing) false

a211 : Action
a211 = registerWakeup
c211 : Configuration
c211 = snapshot (cm6) (g6) (g6) (selecting) 155
  (jobs6) ([]) ([]) 6 (nothing) false

settle : List Action
settle = a209 ∷ a210 ∷ a211 ∷ []
settle-path : Executes c208 settle c211
settle-path = next {c₁ = c209} refl (next {c₁ = c210} refl (next refl done))

suffix : List Action
suffix = round3 ++ (round4 ++ (round5 ++ (round6 ++ settle)))
suffix-path : Executes R.c64 suffix c211
suffix-path = append path3 (append path4 (append path5 (append path6 settle-path)))
schedule : List Action
schedule = R.schedule ++ suffix
path : Executes L.c₀ schedule c211
path = append R.path suffix-path
accepted : traces (Process L.c₀) (map label schedule)
accepted = trace-intro path
step-count : length schedule ≡ 211
step-count = refl
