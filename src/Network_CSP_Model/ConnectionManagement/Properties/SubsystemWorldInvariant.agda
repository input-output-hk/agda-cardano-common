{-# OPTIONS --guardedness #-}

-- Lift runtime/world invariants through all combined-subsystem interleavings.
module ConnectionManagement.Properties.SubsystemWorldInvariant where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
import ConnectionManagement.State as S
open import ConnectionManagement.Store using (Store; lookup; put; delete)
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as Life

import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Properties.PeerJobWorldInvariant as Jobs
open import ConnectionManagement.Subsystem

import ConnectionManagement.Properties.IGTableRetention as Table
open import ConnectionManagement.Properties.HandlerAnchors using (setMux-preserves)

-- IG execution is part of the observation; mutations require table retention.
module Lift
  (Predicate : S.State → IG.Runtime → Set)
  (preserve : ∀ a c {c′} → CM.advance a c ≡ just c′ →
    Predicate (Inbound.world (CM.core c)) (Inbound.inboundGovernor (CM.core c)) →
    Predicate (Inbound.world (CM.core c′)) (Inbound.inboundGovernor (CM.core c′)))
  (ig-preserve : ∀ {s ig ig′} → Table.Retains ig ig′ → Predicate s ig → Predicate s ig′) where

  module Job = Jobs.Lift Predicate preserve ig-preserve

  -- The governor adds no fields to the invariant's observed runtime/world.
  Valid : Configuration → Set
  Valid c = Job.Valid (world c)

  -- All enabled actions are covered; unavailable attempts provide no transition.
  advance-preserves : ∀ a c {c′} → advance a c ≡ just c′ → Valid c → Valid c′
  advance-preserves (core action) c with CM.advance action (J.cm (world c)) in stepped
  ... | nothing = λ ()
  ... | just cm′ = λ { refl v → preserve action (J.cm (world c)) stepped v }
  advance-preserves publishPublicState c with pc c
  ... | publishPublic = λ { refl v → v }
  advance-preserves publishPublicState c | sampleInputs = λ ()
  advance-preserves publishPublicState c | prepareWait = λ ()
  advance-preserves publishPublicState c | selecting = λ ()
  advance-preserves publishPublicState c | (cancelTimer selected) = λ ()
  advance-preserves publishPublicState c | (apply selected) = λ ()
  advance-preserves publishPublicState c | (publishView work) = λ ()
  advance-preserves publishPublicState c | (traceDecision work) = λ ()
  advance-preserves publishPublicState c | (launch work) = λ ()
  advance-preserves publishPublicState c | (register j rest) = λ ()
  advance-preserves publishPublicState c | (completionAssertionFailed result) = λ ()
  advance-preserves (sampleTime t) c with pc c | now c ≤? t
  ... | sampleInputs | yes _ = λ { refl v → v }
  ... | sampleInputs | no _ = λ ()
  advance-preserves (sampleTime t) c | publishPublic | _ = λ ()
  advance-preserves (sampleTime t) c | prepareWait | _ = λ ()
  advance-preserves (sampleTime t) c | selecting | _ = λ ()
  advance-preserves (sampleTime t) c | (cancelTimer selected) | _ = λ ()
  advance-preserves (sampleTime t) c | (apply selected) | _ = λ ()
  advance-preserves (sampleTime t) c | (publishView work) | _ = λ ()
  advance-preserves (sampleTime t) c | (traceDecision work) | _ = λ ()
  advance-preserves (sampleTime t) c | (launch work) | _ = λ ()
  advance-preserves (sampleTime t) c | (register j rest) | _ = λ ()
  advance-preserves (sampleTime t) c | (completionAssertionFailed result) | _ = λ ()
  advance-preserves (setTargets t) c with G.sane t
  ... | true = λ { refl v → v }
  ... | false = λ ()
  advance-preserves (selectMonitor delay) c with pc c | G.monitored (J.peers (world c)) (privateState c)
  ... | selecting | changes@(_ ∷ _) with completeDelays changes delay
  ...   | false = λ ()
  ...   | true = λ { refl v → v }
  advance-preserves (selectMonitor delay) c | selecting | [] = λ ()
  advance-preserves (selectMonitor delay) c | publishPublic | _ = λ ()
  advance-preserves (selectMonitor delay) c | sampleInputs | _ = λ ()
  advance-preserves (selectMonitor delay) c | prepareWait | _ = λ ()
  advance-preserves (selectMonitor delay) c | (cancelTimer selected) | _ = λ ()
  advance-preserves (selectMonitor delay) c | (apply selected) | _ = λ ()
  advance-preserves (selectMonitor delay) c | (publishView work) | _ = λ ()
  advance-preserves (selectMonitor delay) c | (traceDecision work) | _ = λ ()
  advance-preserves (selectMonitor delay) c | (launch work) | _ = λ ()
  advance-preserves (selectMonitor delay) c | (register j rest) | _ = λ ()
  advance-preserves (selectMonitor delay) c | (completionAssertionFailed result) | _ = λ ()
  advance-preserves selectCompletion c with pc c | noMonitor c | completions c
  ... | selecting | true | x ∷ xs = λ { refl v → v }
  ... | selecting | true | [] = λ ()
  ... | selecting | false | _ = λ ()
  advance-preserves selectCompletion c | publishPublic | _ | _ = λ ()
  advance-preserves selectCompletion c | sampleInputs | _ | _ = λ ()
  advance-preserves selectCompletion c | prepareWait | _ | _ = λ ()
  advance-preserves selectCompletion c | (cancelTimer selected) | _ | _ = λ ()
  advance-preserves selectCompletion c | (apply selected) | _ | _ = λ ()
  advance-preserves selectCompletion c | (publishView work) | _ | _ = λ ()
  advance-preserves selectCompletion c | (traceDecision work) | _ | _ = λ ()
  advance-preserves selectCompletion c | (launch work) | _ | _ = λ ()
  advance-preserves selectCompletion c | (register j rest) | _ | _ = λ ()
  advance-preserves selectCompletion c | (completionAssertionFailed result) | _ | _ = λ ()
  advance-preserves selectTargets c with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | false = λ { refl v → v }
  advance-preserves selectTargets c | selecting | true | true | true = λ ()
  advance-preserves selectTargets c | selecting | true | false | true = λ ()
  advance-preserves selectTargets c | selecting | true | false | false = λ ()
  advance-preserves selectTargets c | selecting | false | true | true = λ ()
  advance-preserves selectTargets c | selecting | false | true | false = λ ()
  advance-preserves selectTargets c | selecting | false | false | true = λ ()
  advance-preserves selectTargets c | selecting | false | false | false = λ ()
  advance-preserves selectTargets c | publishPublic | _ | _ | _ = λ ()
  advance-preserves selectTargets c | sampleInputs | _ | _ | _ = λ ()
  advance-preserves selectTargets c | prepareWait | _ | _ | _ = λ ()
  advance-preserves selectTargets c | (cancelTimer selected) | _ | _ | _ = λ ()
  advance-preserves selectTargets c | (apply selected) | _ | _ | _ = λ ()
  advance-preserves selectTargets c | (publishView work) | _ | _ | _ = λ ()
  advance-preserves selectTargets c | (traceDecision work) | _ | _ | _ = λ ()
  advance-preserves selectTargets c | (launch work) | _ | _ | _ = λ ()
  advance-preserves selectTargets c | (register j rest) | _ | _ | _ = λ ()
  advance-preserves selectTargets c | (completionAssertionFailed result) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | true with G.choose (now c) picked (privateState c)
  ...   | nothing = λ ()
  ...   | just d = λ { refl v → v }
  advance-preserves (selectPolicy picked) c | selecting | true | true | false = λ ()
  advance-preserves (selectPolicy picked) c | selecting | true | false | true = λ ()
  advance-preserves (selectPolicy picked) c | selecting | true | false | false = λ ()
  advance-preserves (selectPolicy picked) c | selecting | false | true | true = λ ()
  advance-preserves (selectPolicy picked) c | selecting | false | true | false = λ ()
  advance-preserves (selectPolicy picked) c | selecting | false | false | true = λ ()
  advance-preserves (selectPolicy picked) c | selecting | false | false | false = λ ()
  advance-preserves (selectPolicy picked) c | publishPublic | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c | sampleInputs | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c | prepareWait | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c | (cancelTimer selected) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c | (apply selected) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c | (publishView work) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c | (traceDecision work) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c | (launch work) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c | (register j rest) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c | (completionAssertionFailed result) | _ | _ | _ = λ ()
  advance-preserves registerWakeup c with pc c
  ... | prepareWait = λ { refl v → v }
  advance-preserves registerWakeup c | publishPublic = λ ()
  advance-preserves registerWakeup c | sampleInputs = λ ()
  advance-preserves registerWakeup c | selecting = λ ()
  advance-preserves registerWakeup c | (cancelTimer selected) = λ ()
  advance-preserves registerWakeup c | (apply selected) = λ ()
  advance-preserves registerWakeup c | (publishView work) = λ ()
  advance-preserves registerWakeup c | (traceDecision work) = λ ()
  advance-preserves registerWakeup c | (launch work) = λ ()
  advance-preserves registerWakeup c | (register j rest) = λ ()
  advance-preserves registerWakeup c | (completionAssertionFailed result) = λ ()
  advance-preserves expireWakeup c with pc c | wakeupAt c | wakeupReady c
  ... | selecting | just _ | false = λ { refl v → v }
  ... | selecting | just _ | true = λ ()
  ... | selecting | nothing | _ = λ ()
  advance-preserves expireWakeup c | publishPublic | _ | _ = λ ()
  advance-preserves expireWakeup c | sampleInputs | _ | _ = λ ()
  advance-preserves expireWakeup c | prepareWait | _ | _ = λ ()
  advance-preserves expireWakeup c | (cancelTimer selected) | _ | _ = λ ()
  advance-preserves expireWakeup c | (apply selected) | _ | _ = λ ()
  advance-preserves expireWakeup c | (publishView work) | _ | _ = λ ()
  advance-preserves expireWakeup c | (traceDecision work) | _ | _ = λ ()
  advance-preserves expireWakeup c | (launch work) | _ | _ = λ ()
  advance-preserves expireWakeup c | (register j rest) | _ | _ = λ ()
  advance-preserves expireWakeup c | (completionAssertionFailed result) | _ | _ = λ ()
  advance-preserves cancelWakeup c with pc c
  ... | cancelTimer selected = λ { refl v → v }
  advance-preserves cancelWakeup c | publishPublic = λ ()
  advance-preserves cancelWakeup c | sampleInputs = λ ()
  advance-preserves cancelWakeup c | prepareWait = λ ()
  advance-preserves cancelWakeup c | selecting = λ ()
  advance-preserves cancelWakeup c | (apply selected) = λ ()
  advance-preserves cancelWakeup c | (publishView work) = λ ()
  advance-preserves cancelWakeup c | (traceDecision work) = λ ()
  advance-preserves cancelWakeup c | (launch work) = λ ()
  advance-preserves cancelWakeup c | (register j rest) = λ ()
  advance-preserves cancelWakeup c | (completionAssertionFailed result) = λ ()
  advance-preserves selectWakeup c with pc c | noMonitor c | noCompletions c | noTargets c | wakeupReady c | wakeupAt c | G.firstReady (now c) (privateState c)
  ... | selecting | true | true | true | true | just deadline | nothing = λ { refl v → v }
  ... | selecting | false | _ | _ | _ | _ | _ = λ ()
  ... | selecting | true | false | _ | _ | _ | _ = λ ()
  ... | selecting | true | true | false | _ | _ | _ = λ ()
  ... | selecting | true | true | true | false | _ | _ = λ ()
  ... | selecting | true | true | true | true | nothing | _ = λ ()
  ... | selecting | true | true | true | true | just deadline | just ready = λ ()
  advance-preserves selectWakeup c | publishPublic | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c | sampleInputs | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c | prepareWait | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c | (cancelTimer selected) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c | (apply selected) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c | (publishView work) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c | (traceDecision work) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c | (launch work) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c | (register j rest) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c | (completionAssertionFailed result) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves (applyAt t) c with pc c | now c ≤? t
  ... | apply (policy d) | yes _ = λ { refl v → v }
  ... | apply (completion result) | yes _ with G.completionAssertion result (privateState c)
  ...   | false = λ { refl v → v }
  ...   | true = λ { refl v → v }
  advance-preserves (applyAt t) c | apply (monitor changes delay) | yes _ = λ { refl v → v }
  advance-preserves (applyAt t) c | apply (targets t′) | yes _ = λ { refl v → v }
  advance-preserves (applyAt t) c | apply (wakeup deadline) | yes _ with deadline ≤? t
  ...   | yes _ = λ { refl v → v }
  ...   | no _ = λ ()
  advance-preserves (applyAt t) c | apply (policy d) | no _ = λ ()
  advance-preserves (applyAt t) c | apply (completion result) | no _ = λ ()
  advance-preserves (applyAt t) c | apply (monitor changes delay) | no _ = λ ()
  advance-preserves (applyAt t) c | apply (targets t′) | no _ = λ ()
  advance-preserves (applyAt t) c | apply (wakeup deadline) | no _ = λ ()
  advance-preserves (applyAt t) c | publishPublic | _ = λ ()
  advance-preserves (applyAt t) c | sampleInputs | _ = λ ()
  advance-preserves (applyAt t) c | prepareWait | _ = λ ()
  advance-preserves (applyAt t) c | selecting | _ = λ ()
  advance-preserves (applyAt t) c | (cancelTimer selected) | _ = λ ()
  advance-preserves (applyAt t) c | (publishView work) | _ = λ ()
  advance-preserves (applyAt t) c | (traceDecision work) | _ = λ ()
  advance-preserves (applyAt t) c | (launch work) | _ = λ ()
  advance-preserves (applyAt t) c | (register j rest) | _ = λ ()
  advance-preserves (applyAt t) c | (completionAssertionFailed result) | _ = λ ()
  advance-preserves publishCounters c with pc c
  ... | publishView work = λ { refl v → v }
  advance-preserves publishCounters c | publishPublic = λ ()
  advance-preserves publishCounters c | sampleInputs = λ ()
  advance-preserves publishCounters c | prepareWait = λ ()
  advance-preserves publishCounters c | selecting = λ ()
  advance-preserves publishCounters c | (cancelTimer selected) = λ ()
  advance-preserves publishCounters c | (apply selected) = λ ()
  advance-preserves publishCounters c | (traceDecision work) = λ ()
  advance-preserves publishCounters c | (launch work) = λ ()
  advance-preserves publishCounters c | (register j rest) = λ ()
  advance-preserves publishCounters c | (completionAssertionFailed result) = λ ()
  advance-preserves traceSelection c with pc c
  ... | traceDecision work = λ { refl v → v }
  advance-preserves traceSelection c | publishPublic = λ ()
  advance-preserves traceSelection c | sampleInputs = λ ()
  advance-preserves traceSelection c | prepareWait = λ ()
  advance-preserves traceSelection c | selecting = λ ()
  advance-preserves traceSelection c | (cancelTimer selected) = λ ()
  advance-preserves traceSelection c | (apply selected) = λ ()
  advance-preserves traceSelection c | (publishView work) = λ ()
  advance-preserves traceSelection c | (launch work) = λ ()
  advance-preserves traceSelection c | (register j rest) = λ ()
  advance-preserves traceSelection c | (completionAssertionFailed result) = λ ()
  advance-preserves registerJob c with pc c
  ... | register j rest = λ { refl v → v }
  advance-preserves registerJob c | publishPublic = λ ()
  advance-preserves registerJob c | sampleInputs = λ ()
  advance-preserves registerJob c | prepareWait = λ ()
  advance-preserves registerJob c | selecting = λ ()
  advance-preserves registerJob c | (cancelTimer selected) = λ ()
  advance-preserves registerJob c | (apply selected) = λ ()
  advance-preserves registerJob c | (publishView work) = λ ()
  advance-preserves registerJob c | (traceDecision work) = λ ()
  advance-preserves registerJob c | (launch work) = λ ()
  advance-preserves registerJob c | (completionAssertionFailed result) = λ ()
  advance-preserves (forkJob caller child sock) c with pc c | workerFree caller c
  ... | launch [] | _ = λ ()
  ... | launch (work ∷ rest) | true = λ { refl v → v }
  ... | launch (work ∷ rest) | false = λ ()
  advance-preserves (forkJob caller child sock) c | publishPublic | _ = λ ()
  advance-preserves (forkJob caller child sock) c | sampleInputs | _ = λ ()
  advance-preserves (forkJob caller child sock) c | prepareWait | _ = λ ()
  advance-preserves (forkJob caller child sock) c | selecting | _ = λ ()
  advance-preserves (forkJob caller child sock) c | (cancelTimer selected) | _ = λ ()
  advance-preserves (forkJob caller child sock) c | (apply selected) | _ = λ ()
  advance-preserves (forkJob caller child sock) c | (publishView work) | _ = λ ()
  advance-preserves (forkJob caller child sock) c | (traceDecision work) | _ = λ ()
  advance-preserves (forkJob caller child sock) c | (register j rest) | _ = λ ()
  advance-preserves (forkJob caller child sock) c | (completionAssertionFailed result) | _ = λ ()
  advance-preserves finishLaunch c with pc c
  ... | launch [] = λ { refl v → v }
  ... | launch (work ∷ rest) = λ ()
  advance-preserves finishLaunch c | publishPublic = λ ()
  advance-preserves finishLaunch c | sampleInputs = λ ()
  advance-preserves finishLaunch c | prepareWait = λ ()
  advance-preserves finishLaunch c | selecting = λ ()
  advance-preserves finishLaunch c | (cancelTimer selected) = λ ()
  advance-preserves finishLaunch c | (apply selected) = λ ()
  advance-preserves finishLaunch c | (publishView work) = λ ()
  advance-preserves finishLaunch c | (traceDecision work) = λ ()
  advance-preserves finishLaunch c | (register j rest) = λ ()
  advance-preserves finishLaunch c | (completionAssertionFailed result) = λ ()
  advance-preserves (jobStep j action) c with lookup j (jobs c)
  ... | nothing = λ ()
  ... | just frame with queued frame | J.step action (execution frame) (world c) in stepped
  ...   | false | just (f′ , w′) = λ { refl v → Job.step-preserves action (execution frame) (world c) v stepped }
  ...   | true | _ = λ ()
  ...   | false | nothing = λ ()
  advance-preserves (enqueueCompletion j delay) c with lookup j (jobs c)
  ... | nothing = λ ()
  ... | just frame with queued frame | J.pc (execution frame)
  ...   | false | J.complete result with validCompletionDelay (J.work (execution frame)) result delay
  ...     | false = λ ()
  ...     | true = λ { refl v → v }
  advance-preserves (enqueueCompletion j delay) c | just frame | true | _ = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.begin = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.awaitAcquire = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | (J.startBundle t ns) = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | (J.publishBundle t) = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.markWarm = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.forkMonitor = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.finishActivation = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.awaitHot = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.awaitAll = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.callRelease = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.awaitRelease = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.delayFailure = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | (J.awaitCold result) = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.acquirePolicy = λ ()
  advance-preserves (enqueueCompletion j delay) c | just frame | false | J.nodeDelivery = λ ()
  advance-preserves (deregisterJob j) c with lookup j (jobs c)
  ... | nothing = λ ()
  ... | just frame with queued frame | deregistered frame | any (λ x → does (x ≟ j)) (pool c)
  ...   | true | true | true = λ ()
  ...   | true | true | false = λ ()
  ...   | true | false | true = λ { refl v → v }
  ...   | true | false | false = λ ()
  ...   | false | true | true = λ ()
  ...   | false | true | false = λ ()
  ...   | false | false | true = λ ()
  ...   | false | false | false = λ ()
  advance-preserves (protocolResult ref n result) c with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.step (P.protocolResult n result) peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , ig′) = λ { refl v → v }
  advance-preserves (publishInitiatorResult ref i) c with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.takePending i (P.pendingResults peer) | lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c)))))) in observed
  ...   | just ((n , result) , retained) | just observedMux with Life.muxAllowed (P.muxRef peer) Life.jobAccess (Inbound.handlerLifecycles (CM.core (J.cm (world c))))
  ...     | false = λ ()
  ...     | true = λ { refl v → ig-preserve
    (Table.from-anchors (setMux-preserves (P.muxRef peer) observedMux _
      (Inbound.inboundGovernor (CM.core (J.cm (world c)))) observed refl)) v }
  advance-preserves (publishInitiatorResult ref i) c | just peer | nothing | _ = λ ()
  advance-preserves (publishInitiatorResult ref i) c | just peer | just selected | nothing = λ ()
  advance-preserves (observeInitiatorFailure ref) c with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
  ...   | nothing = λ ()
  ...   | just observedMux with M.completions observedMux
  ...     | M.jobResult M.initiatorJob n (errored err) ∷ rest with CM.advance
    (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c)) in stepped
  ...       | nothing = λ ()
  ...       | just cm′ = λ { refl v → preserve
    (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c)) stepped v }
  advance-preserves (observeInitiatorFailure ref) c | just peer | just observedMux | [] = λ ()
  advance-preserves (observeInitiatorFailure ref) c | just peer | just observedMux | M.jobResult M.responderJob n outcome ∷ rest = λ ()
  advance-preserves (observeInitiatorFailure ref) c | just peer | just observedMux | M.jobResult M.initiatorJob n clean ∷ rest = λ ()
  advance-preserves (pollPeer ref caller) c with lookup ref (J.peers (world c)) | lookup ref (monitors c)
  ... | just peer | nothing with P.monitorStarted peer | P.status peer
  ...   | true | P.peerCooling with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...     | nothing = λ ()
  ...     | just (peer′ , _) = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c | just peer | nothing | true | P.peerCold = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c | just peer | nothing | true | P.peerWarm with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl v → v }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c | just peer | nothing | true | P.peerHot with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl v → v }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c | just peer | nothing | false | _ = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f with J.pc f
  ... | J.awaitCold _ with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , _) = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.begin = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.awaitAcquire = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | (J.startBundle t ns) = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | (J.publishBundle t) = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.markWarm = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.forkMonitor = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.finishActivation = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.awaitHot = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.awaitAll = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.callRelease = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.awaitRelease = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.delayFailure = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | (J.complete result) = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.acquirePolicy = λ ()
  advance-preserves (pollPeer ref caller) c | just peer | just f | J.nodeDelivery = λ ()
  advance-preserves (pollPeer ref caller) c | nothing | _ = λ ()
  advance-preserves (monitorStep ref action) c with lookup ref (monitors c)
  ... | nothing = λ ()
  ... | just f with J.step action f (world c) in stepped
  ...   | nothing = λ ()
  ...   | just (f′ , w′) = λ { refl v → Job.step-preserves action f (world c) v stepped }
  advance-preserves (monitorFinished ref) c with lookup ref (monitors c)
  ... | nothing = λ ()
  ... | just f with J.pc f
  ...   | J.complete _ = λ { refl v → v }
  ...   | J.begin = λ ()
  ...   | J.awaitAcquire = λ ()
  ...   | (J.startBundle t ns) = λ ()
  ...   | (J.publishBundle t) = λ ()
  ...   | J.markWarm = λ ()
  ...   | J.forkMonitor = λ ()
  ...   | J.finishActivation = λ ()
  ...   | J.awaitHot = λ ()
  ...   | J.awaitAll = λ ()
  ...   | J.callRelease = λ ()
  ...   | J.awaitRelease = λ ()
  ...   | J.delayFailure = λ ()
  ...   | (J.awaitCold result) = λ ()
  ...   | J.acquirePolicy = λ ()
  ...   | J.nodeDelivery = λ ()
  -- No restriction on which jobs, monitors or core callers interleave.
  exec-preserves : ∀ {c actions c′} → Valid c → Executes c actions c′ → Valid c′
  exec-preserves valid done = valid
  exec-preserves valid (next {c = c} {a = a} eq rest) =
    exec-preserves (advance-preserves a c eq valid) rest
