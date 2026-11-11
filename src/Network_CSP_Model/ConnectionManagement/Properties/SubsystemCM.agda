{-# OPTIONS --guardedness #-}

-- Lift an invariant over the whole CM configuration through all combined
-- subsystem interleavings (see PeerJobCM for the job layer).
module ConnectionManagement.Properties.SubsystemCM where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
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
import ConnectionManagement.Properties.MachineQuiet as Quiet
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as Life

import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Properties.PeerJobCM as Jobs
open import ConnectionManagement.Subsystem

-- A restricted source observer reuses every non-core subsystem case.
-- A restricted source observer reuses every non-core subsystem case.
-- The old unrestricted interface remains available below.
module StepLift
  (Predicate : CM.Configuration → Set)
  (ig-write : ∀ c g → Quiet.SameControl (Inbound.inboundGovernor (CM.core c)) g → Predicate c → Predicate (record c { core = record (CM.core c) { inboundGovernor = g } }))
  (job-preserve : ∀ a f w → Predicate (J.cm w) →
    ∀ {out} → J.step a f w ≡ just out →
    Predicate (J.cm (Data.Product.proj₂ out)))
  (monitor-preserve : ∀ mid c {c′} → CM.advance (CM.inbound (Inbound.igStep (IG.monitorCompletion mid))) c ≡ just c′ →
    Predicate c →
    Predicate c′)
  (PermitCore : CM.Action → Set)
  (core-preserve : ∀ a c {c′} → PermitCore a → CM.advance a c ≡ just c′ →
    Predicate c →
    Predicate c′) where

  -- Only the raw core constructor needs an explicit source permission.
  Allowed : Action → Set
  Allowed (core action) = PermitCore action
  Allowed _ = ⊤

  Valid : Configuration → Set
  Valid c = Predicate (J.cm (world c))

  -- All enabled actions are covered; unavailable attempts provide no transition.
  advance-preserves : ∀ a c {c′} → Allowed a → advance a c ≡ just c′ → Valid c → Valid c′
  advance-preserves (core action) c permission with CM.advance action (J.cm (world c)) in stepped
  ... | nothing = λ ()
  ... | just cm′ = λ { refl v → core-preserve action (J.cm (world c)) permission stepped v }
  advance-preserves publishPublicState c permission with pc c
  ... | publishPublic = λ { refl v → v }
  advance-preserves publishPublicState c permission | sampleInputs = λ ()
  advance-preserves publishPublicState c permission | prepareWait = λ ()
  advance-preserves publishPublicState c permission | selecting = λ ()
  advance-preserves publishPublicState c permission | (cancelTimer selected) = λ ()
  advance-preserves publishPublicState c permission | (apply selected) = λ ()
  advance-preserves publishPublicState c permission | (publishView work) = λ ()
  advance-preserves publishPublicState c permission | (traceDecision work) = λ ()
  advance-preserves publishPublicState c permission | (launch work) = λ ()
  advance-preserves publishPublicState c permission | (register j rest) = λ ()
  advance-preserves publishPublicState c permission | (completionAssertionFailed result) = λ ()
  advance-preserves (sampleTime t) c permission with pc c | now c ≤? t
  ... | sampleInputs | yes _ = λ { refl v → v }
  ... | sampleInputs | no _ = λ ()
  advance-preserves (sampleTime t) c permission | publishPublic | _ = λ ()
  advance-preserves (sampleTime t) c permission | prepareWait | _ = λ ()
  advance-preserves (sampleTime t) c permission | selecting | _ = λ ()
  advance-preserves (sampleTime t) c permission | (cancelTimer selected) | _ = λ ()
  advance-preserves (sampleTime t) c permission | (apply selected) | _ = λ ()
  advance-preserves (sampleTime t) c permission | (publishView work) | _ = λ ()
  advance-preserves (sampleTime t) c permission | (traceDecision work) | _ = λ ()
  advance-preserves (sampleTime t) c permission | (launch work) | _ = λ ()
  advance-preserves (sampleTime t) c permission | (register j rest) | _ = λ ()
  advance-preserves (sampleTime t) c permission | (completionAssertionFailed result) | _ = λ ()
  -- Raw target-input writes do not affect the observed CM/IG predicate.
  advance-preserves (setTargets t) c permission = λ { refl v → v }
  advance-preserves (selectMonitor delay) c permission with pc c | G.monitored (J.peers (world c)) (privateState c)
  ... | selecting | changes@(_ ∷ _) with completeDelays changes delay
  ...   | false = λ ()
  ...   | true = λ { refl v → v }
  advance-preserves (selectMonitor delay) c permission | selecting | [] = λ ()
  advance-preserves (selectMonitor delay) c permission | publishPublic | _ = λ ()
  advance-preserves (selectMonitor delay) c permission | sampleInputs | _ = λ ()
  advance-preserves (selectMonitor delay) c permission | prepareWait | _ = λ ()
  advance-preserves (selectMonitor delay) c permission | (cancelTimer selected) | _ = λ ()
  advance-preserves (selectMonitor delay) c permission | (apply selected) | _ = λ ()
  advance-preserves (selectMonitor delay) c permission | (publishView work) | _ = λ ()
  advance-preserves (selectMonitor delay) c permission | (traceDecision work) | _ = λ ()
  advance-preserves (selectMonitor delay) c permission | (launch work) | _ = λ ()
  advance-preserves (selectMonitor delay) c permission | (register j rest) | _ = λ ()
  advance-preserves (selectMonitor delay) c permission | (completionAssertionFailed result) | _ = λ ()
  advance-preserves selectCompletion c permission with pc c | noMonitor c | completions c
  ... | selecting | true | x ∷ xs = λ { refl v → v }
  ... | selecting | true | [] = λ ()
  ... | selecting | false | _ = λ ()
  advance-preserves selectCompletion c permission | publishPublic | _ | _ = λ ()
  advance-preserves selectCompletion c permission | sampleInputs | _ | _ = λ ()
  advance-preserves selectCompletion c permission | prepareWait | _ | _ = λ ()
  advance-preserves selectCompletion c permission | (cancelTimer selected) | _ | _ = λ ()
  advance-preserves selectCompletion c permission | (apply selected) | _ | _ = λ ()
  advance-preserves selectCompletion c permission | (publishView work) | _ | _ = λ ()
  advance-preserves selectCompletion c permission | (traceDecision work) | _ | _ = λ ()
  advance-preserves selectCompletion c permission | (launch work) | _ | _ = λ ()
  advance-preserves selectCompletion c permission | (register j rest) | _ | _ = λ ()
  advance-preserves selectCompletion c permission | (completionAssertionFailed result) | _ | _ = λ ()
  advance-preserves selectTargets c permission with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | false = λ { refl v → v }
  advance-preserves selectTargets c permission | selecting | true | true | true = λ ()
  advance-preserves selectTargets c permission | selecting | true | false | true = λ ()
  advance-preserves selectTargets c permission | selecting | true | false | false = λ ()
  advance-preserves selectTargets c permission | selecting | false | true | true = λ ()
  advance-preserves selectTargets c permission | selecting | false | true | false = λ ()
  advance-preserves selectTargets c permission | selecting | false | false | true = λ ()
  advance-preserves selectTargets c permission | selecting | false | false | false = λ ()
  advance-preserves selectTargets c permission | publishPublic | _ | _ | _ = λ ()
  advance-preserves selectTargets c permission | sampleInputs | _ | _ | _ = λ ()
  advance-preserves selectTargets c permission | prepareWait | _ | _ | _ = λ ()
  advance-preserves selectTargets c permission | (cancelTimer selected) | _ | _ | _ = λ ()
  advance-preserves selectTargets c permission | (apply selected) | _ | _ | _ = λ ()
  advance-preserves selectTargets c permission | (publishView work) | _ | _ | _ = λ ()
  advance-preserves selectTargets c permission | (traceDecision work) | _ | _ | _ = λ ()
  advance-preserves selectTargets c permission | (launch work) | _ | _ | _ = λ ()
  advance-preserves selectTargets c permission | (register j rest) | _ | _ | _ = λ ()
  advance-preserves selectTargets c permission | (completionAssertionFailed result) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | true with G.choose (now c) picked (privateState c)
  ...   | nothing = λ ()
  ...   | just d = λ { refl v → v }
  advance-preserves (selectPolicy picked) c permission | selecting | true | true | false = λ ()
  advance-preserves (selectPolicy picked) c permission | selecting | true | false | true = λ ()
  advance-preserves (selectPolicy picked) c permission | selecting | true | false | false = λ ()
  advance-preserves (selectPolicy picked) c permission | selecting | false | true | true = λ ()
  advance-preserves (selectPolicy picked) c permission | selecting | false | true | false = λ ()
  advance-preserves (selectPolicy picked) c permission | selecting | false | false | true = λ ()
  advance-preserves (selectPolicy picked) c permission | selecting | false | false | false = λ ()
  advance-preserves (selectPolicy picked) c permission | publishPublic | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission | sampleInputs | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission | prepareWait | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission | (cancelTimer selected) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission | (apply selected) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission | (publishView work) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission | (traceDecision work) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission | (launch work) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission | (register j rest) | _ | _ | _ = λ ()
  advance-preserves (selectPolicy picked) c permission | (completionAssertionFailed result) | _ | _ | _ = λ ()
  advance-preserves registerWakeup c permission with pc c
  ... | prepareWait = λ { refl v → v }
  advance-preserves registerWakeup c permission | publishPublic = λ ()
  advance-preserves registerWakeup c permission | sampleInputs = λ ()
  advance-preserves registerWakeup c permission | selecting = λ ()
  advance-preserves registerWakeup c permission | (cancelTimer selected) = λ ()
  advance-preserves registerWakeup c permission | (apply selected) = λ ()
  advance-preserves registerWakeup c permission | (publishView work) = λ ()
  advance-preserves registerWakeup c permission | (traceDecision work) = λ ()
  advance-preserves registerWakeup c permission | (launch work) = λ ()
  advance-preserves registerWakeup c permission | (register j rest) = λ ()
  advance-preserves registerWakeup c permission | (completionAssertionFailed result) = λ ()
  advance-preserves expireWakeup c permission with pc c | wakeupAt c | wakeupReady c
  ... | selecting | just _ | false = λ { refl v → v }
  ... | selecting | just _ | true = λ ()
  ... | selecting | nothing | _ = λ ()
  advance-preserves expireWakeup c permission | publishPublic | _ | _ = λ ()
  advance-preserves expireWakeup c permission | sampleInputs | _ | _ = λ ()
  advance-preserves expireWakeup c permission | prepareWait | _ | _ = λ ()
  advance-preserves expireWakeup c permission | (cancelTimer selected) | _ | _ = λ ()
  advance-preserves expireWakeup c permission | (apply selected) | _ | _ = λ ()
  advance-preserves expireWakeup c permission | (publishView work) | _ | _ = λ ()
  advance-preserves expireWakeup c permission | (traceDecision work) | _ | _ = λ ()
  advance-preserves expireWakeup c permission | (launch work) | _ | _ = λ ()
  advance-preserves expireWakeup c permission | (register j rest) | _ | _ = λ ()
  advance-preserves expireWakeup c permission | (completionAssertionFailed result) | _ | _ = λ ()
  advance-preserves cancelWakeup c permission with pc c
  ... | cancelTimer selected = λ { refl v → v }
  advance-preserves cancelWakeup c permission | publishPublic = λ ()
  advance-preserves cancelWakeup c permission | sampleInputs = λ ()
  advance-preserves cancelWakeup c permission | prepareWait = λ ()
  advance-preserves cancelWakeup c permission | selecting = λ ()
  advance-preserves cancelWakeup c permission | (apply selected) = λ ()
  advance-preserves cancelWakeup c permission | (publishView work) = λ ()
  advance-preserves cancelWakeup c permission | (traceDecision work) = λ ()
  advance-preserves cancelWakeup c permission | (launch work) = λ ()
  advance-preserves cancelWakeup c permission | (register j rest) = λ ()
  advance-preserves cancelWakeup c permission | (completionAssertionFailed result) = λ ()
  advance-preserves selectWakeup c permission with pc c | noMonitor c | noCompletions c | noTargets c | wakeupReady c | wakeupAt c | G.firstReady (now c) (privateState c)
  ... | selecting | true | true | true | true | just deadline | nothing = λ { refl v → v }
  ... | selecting | false | _ | _ | _ | _ | _ = λ ()
  ... | selecting | true | false | _ | _ | _ | _ = λ ()
  ... | selecting | true | true | false | _ | _ | _ = λ ()
  ... | selecting | true | true | true | false | _ | _ = λ ()
  ... | selecting | true | true | true | true | nothing | _ = λ ()
  ... | selecting | true | true | true | true | just deadline | just ready = λ ()
  advance-preserves selectWakeup c permission | publishPublic | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c permission | sampleInputs | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c permission | prepareWait | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c permission | (cancelTimer selected) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c permission | (apply selected) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c permission | (publishView work) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c permission | (traceDecision work) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c permission | (launch work) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c permission | (register j rest) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves selectWakeup c permission | (completionAssertionFailed result) | _ | _ | _ | _ | _ | _ = λ ()
  advance-preserves (applyAt t) c permission with pc c | now c ≤? t
  ... | apply (policy d) | yes _ = λ { refl v → v }
  ... | apply (completion result) | yes _ with G.completionAssertion result (privateState c)
  ...   | false = λ { refl v → v }
  ...   | true = λ { refl v → v }
  advance-preserves (applyAt t) c permission | apply (monitor changes delay) | yes _ = λ { refl v → v }
  advance-preserves (applyAt t) c permission | apply (targets t′) | yes _ = λ { refl v → v }
  advance-preserves (applyAt t) c permission | apply (wakeup deadline) | yes _ with deadline ≤? t
  ...   | yes _ = λ { refl v → v }
  ...   | no _ = λ ()
  advance-preserves (applyAt t) c permission | apply (policy d) | no _ = λ ()
  advance-preserves (applyAt t) c permission | apply (completion result) | no _ = λ ()
  advance-preserves (applyAt t) c permission | apply (monitor changes delay) | no _ = λ ()
  advance-preserves (applyAt t) c permission | apply (targets t′) | no _ = λ ()
  advance-preserves (applyAt t) c permission | apply (wakeup deadline) | no _ = λ ()
  advance-preserves (applyAt t) c permission | publishPublic | _ = λ ()
  advance-preserves (applyAt t) c permission | sampleInputs | _ = λ ()
  advance-preserves (applyAt t) c permission | prepareWait | _ = λ ()
  advance-preserves (applyAt t) c permission | selecting | _ = λ ()
  advance-preserves (applyAt t) c permission | (cancelTimer selected) | _ = λ ()
  advance-preserves (applyAt t) c permission | (publishView work) | _ = λ ()
  advance-preserves (applyAt t) c permission | (traceDecision work) | _ = λ ()
  advance-preserves (applyAt t) c permission | (launch work) | _ = λ ()
  advance-preserves (applyAt t) c permission | (register j rest) | _ = λ ()
  advance-preserves (applyAt t) c permission | (completionAssertionFailed result) | _ = λ ()
  advance-preserves publishCounters c permission with pc c
  ... | publishView work = λ { refl v → v }
  advance-preserves publishCounters c permission | publishPublic = λ ()
  advance-preserves publishCounters c permission | sampleInputs = λ ()
  advance-preserves publishCounters c permission | prepareWait = λ ()
  advance-preserves publishCounters c permission | selecting = λ ()
  advance-preserves publishCounters c permission | (cancelTimer selected) = λ ()
  advance-preserves publishCounters c permission | (apply selected) = λ ()
  advance-preserves publishCounters c permission | (traceDecision work) = λ ()
  advance-preserves publishCounters c permission | (launch work) = λ ()
  advance-preserves publishCounters c permission | (register j rest) = λ ()
  advance-preserves publishCounters c permission | (completionAssertionFailed result) = λ ()
  advance-preserves traceSelection c permission with pc c
  ... | traceDecision work = λ { refl v → v }
  advance-preserves traceSelection c permission | publishPublic = λ ()
  advance-preserves traceSelection c permission | sampleInputs = λ ()
  advance-preserves traceSelection c permission | prepareWait = λ ()
  advance-preserves traceSelection c permission | selecting = λ ()
  advance-preserves traceSelection c permission | (cancelTimer selected) = λ ()
  advance-preserves traceSelection c permission | (apply selected) = λ ()
  advance-preserves traceSelection c permission | (publishView work) = λ ()
  advance-preserves traceSelection c permission | (launch work) = λ ()
  advance-preserves traceSelection c permission | (register j rest) = λ ()
  advance-preserves traceSelection c permission | (completionAssertionFailed result) = λ ()
  advance-preserves registerJob c permission with pc c
  ... | register j rest = λ { refl v → v }
  advance-preserves registerJob c permission | publishPublic = λ ()
  advance-preserves registerJob c permission | sampleInputs = λ ()
  advance-preserves registerJob c permission | prepareWait = λ ()
  advance-preserves registerJob c permission | selecting = λ ()
  advance-preserves registerJob c permission | (cancelTimer selected) = λ ()
  advance-preserves registerJob c permission | (apply selected) = λ ()
  advance-preserves registerJob c permission | (publishView work) = λ ()
  advance-preserves registerJob c permission | (traceDecision work) = λ ()
  advance-preserves registerJob c permission | (launch work) = λ ()
  advance-preserves registerJob c permission | (completionAssertionFailed result) = λ ()
  advance-preserves (forkJob caller child sock) c permission with pc c | workerFree caller c
  ... | launch [] | _ = λ ()
  ... | launch (work ∷ rest) | true = λ { refl v → v }
  ... | launch (work ∷ rest) | false = λ ()
  advance-preserves (forkJob caller child sock) c permission | publishPublic | _ = λ ()
  advance-preserves (forkJob caller child sock) c permission | sampleInputs | _ = λ ()
  advance-preserves (forkJob caller child sock) c permission | prepareWait | _ = λ ()
  advance-preserves (forkJob caller child sock) c permission | selecting | _ = λ ()
  advance-preserves (forkJob caller child sock) c permission | (cancelTimer selected) | _ = λ ()
  advance-preserves (forkJob caller child sock) c permission | (apply selected) | _ = λ ()
  advance-preserves (forkJob caller child sock) c permission | (publishView work) | _ = λ ()
  advance-preserves (forkJob caller child sock) c permission | (traceDecision work) | _ = λ ()
  advance-preserves (forkJob caller child sock) c permission | (register j rest) | _ = λ ()
  advance-preserves (forkJob caller child sock) c permission | (completionAssertionFailed result) | _ = λ ()
  advance-preserves finishLaunch c permission with pc c
  ... | launch [] = λ { refl v → v }
  ... | launch (work ∷ rest) = λ ()
  advance-preserves finishLaunch c permission | publishPublic = λ ()
  advance-preserves finishLaunch c permission | sampleInputs = λ ()
  advance-preserves finishLaunch c permission | prepareWait = λ ()
  advance-preserves finishLaunch c permission | selecting = λ ()
  advance-preserves finishLaunch c permission | (cancelTimer selected) = λ ()
  advance-preserves finishLaunch c permission | (apply selected) = λ ()
  advance-preserves finishLaunch c permission | (publishView work) = λ ()
  advance-preserves finishLaunch c permission | (traceDecision work) = λ ()
  advance-preserves finishLaunch c permission | (register j rest) = λ ()
  advance-preserves finishLaunch c permission | (completionAssertionFailed result) = λ ()
  advance-preserves (jobStep j action) c permission with lookup j (jobs c)
  ... | nothing = λ ()
  ... | just frame with queued frame | J.step action (execution frame) (world c) in stepped
  ...   | false | just (f′ , w′) = λ { refl v → job-preserve action (execution frame) (world c) v stepped }
  ...   | true | _ = λ ()
  ...   | false | nothing = λ ()
  advance-preserves (enqueueCompletion j delay) c permission with lookup j (jobs c)
  ... | nothing = λ ()
  ... | just frame with queued frame | J.pc (execution frame)
  ...   | false | J.complete result with validCompletionDelay (J.work (execution frame)) result delay
  ...     | false = λ ()
  ...     | true = λ { refl v → v }
  advance-preserves (enqueueCompletion j delay) c permission | just frame | true | _ = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.begin = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.awaitAcquire = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | (J.startBundle t ns) = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | (J.publishBundle t) = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.markWarm = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.forkMonitor = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.finishActivation = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.awaitHot = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.awaitAll = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.callRelease = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.awaitRelease = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | J.delayFailure = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | (J.awaitCold result) = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | (J.acquirePolicy fault) = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | (J.nodeDelivery fault) = λ ()
  advance-preserves (enqueueCompletion j delay) c permission | just frame | false | (J.nodeRethrow fault) = λ ()
  advance-preserves (deregisterJob j) c permission with lookup j (jobs c)
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
  advance-preserves (protocolResult ref n result) c permission with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.step (P.protocolResult n result) peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , ig′) = λ { refl v → v }
  advance-preserves (publishInitiatorResult ref i) c permission with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.takePending i (P.pendingResults peer) | lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
  ...   | just ((n , result) , retained) | just observedMux with Life.muxAllowed (P.muxRef peer) Life.jobAccess (Inbound.handlerLifecycles (CM.core (J.cm (world c))))
  ...     | false = λ ()
  ...     | true = λ { refl v → ig-write (J.cm (world c)) _ (refl , refl) v }
  advance-preserves (publishInitiatorResult ref i) c permission | just peer | nothing | _ = λ ()
  advance-preserves (publishInitiatorResult ref i) c permission | just peer | just selected | nothing = λ ()
  advance-preserves (observeInitiatorFailure ref) c permission with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
  ...   | nothing = λ ()
  ...   | just observedMux with M.completions observedMux
  ...     | M.jobResult M.initiatorJob n (errored err) ∷ rest with CM.advance
    (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c)) in stepped
  ...       | nothing = λ ()
  ...       | just cm′ = λ { refl v → monitor-preserve (P.muxRef peer) (J.cm (world c)) stepped v }
  advance-preserves (observeInitiatorFailure ref) c permission | just peer | just observedMux | [] = λ ()
  advance-preserves (observeInitiatorFailure ref) c permission | just peer | just observedMux | M.jobResult M.responderJob n outcome ∷ rest = λ ()
  advance-preserves (observeInitiatorFailure ref) c permission | just peer | just observedMux | M.jobResult M.initiatorJob n clean ∷ rest = λ ()
  advance-preserves (pollPeer ref caller) c permission with lookup ref (J.peers (world c)) | lookup ref (monitors c)
  ... | just peer | nothing with P.monitorStarted peer | P.status peer
  ...   | true | P.peerCooling with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...     | nothing = λ ()
  ...     | just (peer′ , _) = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c permission | just peer | nothing | true | P.peerCold = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c permission | just peer | nothing | true | P.peerWarm with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl v → v }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c permission | just peer | nothing | true | P.peerHot with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl v → v }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c permission | just peer | nothing | false | _ = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f with J.pc f
  ... | J.awaitCold _ with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , _) = λ { refl v → v }
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.begin = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.awaitAcquire = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | (J.startBundle t ns) = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | (J.publishBundle t) = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.markWarm = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.forkMonitor = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.finishActivation = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.awaitHot = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.awaitAll = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.callRelease = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.awaitRelease = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | J.delayFailure = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | (J.complete result) = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | (J.acquirePolicy fault) = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | (J.nodeDelivery fault) = λ ()
  advance-preserves (pollPeer ref caller) c permission | just peer | just f | (J.nodeRethrow fault) = λ ()
  advance-preserves (pollPeer ref caller) c permission | nothing | _ = λ ()
  advance-preserves (monitorStep ref action) c permission with lookup ref (monitors c)
  ... | nothing = λ ()
  ... | just f with J.step action f (world c) in stepped
  ...   | nothing = λ ()
  ...   | just (f′ , w′) = λ { refl v → job-preserve action f (world c) v stepped }
  advance-preserves (monitorFinished ref) c permission with lookup ref (monitors c)
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
  ...   | (J.acquirePolicy fault) = λ ()
  ...   | (J.nodeDelivery fault) = λ ()
  ...   | (J.nodeRethrow fault) = λ ()
  -- No restriction on which jobs, monitors or core callers interleave.

