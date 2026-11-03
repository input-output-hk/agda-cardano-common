{-# OPTIONS --guardedness #-}

-- Completion-queue effects and returned-body agreement in peer supervision.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.GovernorCompletions (isIOManagerError : ErrorId → Bool) where
open import Data.Bool using (true; false; _∧_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain hiding (job)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.GovernorPool as Governor
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.OutboundMachine as CM
private
 module GP = Governor isIOManagerError
 module Pool = GP.Pool
 module PS = Supervision isIOManagerError
 module GPool = GP.Pool
 module BPool = PS.Pool

-- Source job rows, the pending FIFO and the governor pool suffice for
-- publication provenance. CM state is deliberately absent.
record View : Set where
 constructor queueView
 field frames : Store JobId Sub.JobFrame
       pending : List G.Completion
       pool : Pool.State
 handles : Store JobId Pool.ThreadPhase
 handles = Pool.handles pool
viewG : GP.State → View
viewG s = queueView (Sub.jobs (GP.machine s)) (Sub.completions (GP.machine s)) (GP.pool s)
view : PS.State → View
view s = viewG (PS.governor s)
record Publication (before : View) (result : G.Completion) : Set where
 constructor publication
 field job : JobId
       frame : Sub.JobFrame
       payload : GP.Body
       found : lookup job (View.frames before) ≡ just frame
       completed : J.pc (Sub.execution frame) ≡ J.complete (G.outcome result)
       work : J.work (Sub.execution frame) ≡ G.work result
       returned : lookup job (View.handles before) ≡ just (Pool.bodyReturned payload)
       agrees : does (job ≟ GP.identity payload) ∧ GP.sameJob (G.work result) (GP.work payload) ∧ GP.sameOutcome (G.outcome result) (GP.outcome payload) ≡ true

data Change (before after : View) : Set where
 kept : View.pending after ≡ View.pending before → Change before after
 taken : ∀ x xs → View.pending before ≡ x ∷ xs → View.pending after ≡ xs → Change before after
 added : ∀ result (published : Publication before result) →
   View.pending after ≡ View.pending before ++ (result ∷ []) →
   Pool.step (Pool.publishCompletion (Publication.job published)) (View.pool before) ≡ just (View.pool after) → Change before after

-- Backing values are transported by view equality, never by rewriting CM state.
right-view : ∀ {before after next} → after ≡ next → Change before after → Change before next
right-view refl evidence = evidence

module Queue where
  open import Data.Bool using (true; false)
  open import Data.Nat using (ℕ; suc; _≤?_)
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.Bool.ListAction using (any)
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (_,_)
  open import Relation.Nullary using (yes; no; does)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Class.DecEq using (_≟_)
  open import ConnectionManagement.Domain hiding (job)
  open import ConnectionManagement.IGTypes using (clean; errored)
  open import ConnectionManagement.Store using (lookup)
  import ConnectionManagement.Subsystem as Sub
  open Sub
  import ConnectionManagement.Rules.OutboundGovernor as G
  import ConnectionManagement.Rules.PeerJobs as J
  import ConnectionManagement.Rules.PeerActions as P
  import ConnectionManagement.OutboundMachine as CM
  import ConnectionManagement.Machine as Inbound
  import ConnectionManagement.Rules.IGRegistration as IG
  import ConnectionManagement.Rules.MuxRuntime as M
  import ConnectionManagement.Rules.HandlerLifecycle as Life

  -- Queue effects cover every enabled subsystem operation, including retries,
  -- rather than imposing a whitelist on which actors may interleave.
  data QueueStep : Action → Configuration → Configuration → Set where
   q-retained : ∀ {a c d} → completions d ≡ completions c → QueueStep a c d
   q-consumed : ∀ {c d} x xs → completions c ≡ x ∷ xs → completions d ≡ xs → QueueStep selectCompletion c d
   q-appended : ∀ {c d} j delay frame result → lookup j (jobs c) ≡ just frame → J.pc (execution frame) ≡ J.complete result →
    completions d ≡ completions c ++ (G.completion (J.work (execution frame)) result delay ∷ []) → QueueStep (enqueueCompletion j delay) c d
  queue-step : ∀ a c {d} → advance a c ≡ just d → QueueStep a c d
  queue-step (core action) c with CM.advance action (J.cm (world c)) in stepped
  ... | nothing = λ ()
  ... | just cm′ = λ { refl → q-retained refl }
  queue-step publishPublicState c with pc c
  ... | publishPublic = λ { refl → q-retained refl }
  queue-step publishPublicState c | sampleInputs = λ ()
  queue-step publishPublicState c | prepareWait = λ ()
  queue-step publishPublicState c | selecting = λ ()
  queue-step publishPublicState c | (cancelTimer selected) = λ ()
  queue-step publishPublicState c | (apply selected) = λ ()
  queue-step publishPublicState c | (publishView work) = λ ()
  queue-step publishPublicState c | (traceDecision work) = λ ()
  queue-step publishPublicState c | (launch work) = λ ()
  queue-step publishPublicState c | (register j rest) = λ ()
  queue-step publishPublicState c | (completionAssertionFailed result) = λ ()
  queue-step (sampleTime t) c with pc c | now c ≤? t
  ... | sampleInputs | yes _ = λ { refl → q-retained refl }
  ... | sampleInputs | no _ = λ ()
  queue-step (sampleTime t) c | publishPublic | _ = λ ()
  queue-step (sampleTime t) c | prepareWait | _ = λ ()
  queue-step (sampleTime t) c | selecting | _ = λ ()
  queue-step (sampleTime t) c | (cancelTimer selected) | _ = λ ()
  queue-step (sampleTime t) c | (apply selected) | _ = λ ()
  queue-step (sampleTime t) c | (publishView work) | _ = λ ()
  queue-step (sampleTime t) c | (traceDecision work) | _ = λ ()
  queue-step (sampleTime t) c | (launch work) | _ = λ ()
  queue-step (sampleTime t) c | (register j rest) | _ = λ ()
  queue-step (sampleTime t) c | (completionAssertionFailed result) | _ = λ ()
  -- Raw target-input writes do not alter the completion FIFO.
  queue-step (setTargets t) c = λ { refl → q-retained refl }
  queue-step (selectMonitor delay) c with pc c | G.monitored (J.peers (world c)) (privateState c)
  ... | selecting | changes@(_ ∷ _) with completeDelays changes delay
  ...   | false = λ ()
  ...   | true = λ { refl → q-retained refl }
  queue-step (selectMonitor delay) c | selecting | [] = λ ()
  queue-step (selectMonitor delay) c | publishPublic | _ = λ ()
  queue-step (selectMonitor delay) c | sampleInputs | _ = λ ()
  queue-step (selectMonitor delay) c | prepareWait | _ = λ ()
  queue-step (selectMonitor delay) c | (cancelTimer selected) | _ = λ ()
  queue-step (selectMonitor delay) c | (apply selected) | _ = λ ()
  queue-step (selectMonitor delay) c | (publishView work) | _ = λ ()
  queue-step (selectMonitor delay) c | (traceDecision work) | _ = λ ()
  queue-step (selectMonitor delay) c | (launch work) | _ = λ ()
  queue-step (selectMonitor delay) c | (register j rest) | _ = λ ()
  queue-step (selectMonitor delay) c | (completionAssertionFailed result) | _ = λ ()
  queue-step selectCompletion c with pc c | noMonitor c | completions c in fifo
  ... | selecting | true | x ∷ xs = λ { refl → q-consumed x xs fifo refl }
  ... | selecting | true | [] = λ ()
  ... | selecting | false | _ = λ ()
  queue-step selectCompletion c | publishPublic | _ | _ = λ ()
  queue-step selectCompletion c | sampleInputs | _ | _ = λ ()
  queue-step selectCompletion c | prepareWait | _ | _ = λ ()
  queue-step selectCompletion c | (cancelTimer selected) | _ | _ = λ ()
  queue-step selectCompletion c | (apply selected) | _ | _ = λ ()
  queue-step selectCompletion c | (publishView work) | _ | _ = λ ()
  queue-step selectCompletion c | (traceDecision work) | _ | _ = λ ()
  queue-step selectCompletion c | (launch work) | _ | _ = λ ()
  queue-step selectCompletion c | (register j rest) | _ | _ = λ ()
  queue-step selectCompletion c | (completionAssertionFailed result) | _ | _ = λ ()
  queue-step selectTargets c with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | false = λ { refl → q-retained refl }
  queue-step selectTargets c | selecting | true | true | true = λ ()
  queue-step selectTargets c | selecting | true | false | true = λ ()
  queue-step selectTargets c | selecting | true | false | false = λ ()
  queue-step selectTargets c | selecting | false | true | true = λ ()
  queue-step selectTargets c | selecting | false | true | false = λ ()
  queue-step selectTargets c | selecting | false | false | true = λ ()
  queue-step selectTargets c | selecting | false | false | false = λ ()
  queue-step selectTargets c | publishPublic | _ | _ | _ = λ ()
  queue-step selectTargets c | sampleInputs | _ | _ | _ = λ ()
  queue-step selectTargets c | prepareWait | _ | _ | _ = λ ()
  queue-step selectTargets c | (cancelTimer selected) | _ | _ | _ = λ ()
  queue-step selectTargets c | (apply selected) | _ | _ | _ = λ ()
  queue-step selectTargets c | (publishView work) | _ | _ | _ = λ ()
  queue-step selectTargets c | (traceDecision work) | _ | _ | _ = λ ()
  queue-step selectTargets c | (launch work) | _ | _ | _ = λ ()
  queue-step selectTargets c | (register j rest) | _ | _ | _ = λ ()
  queue-step selectTargets c | (completionAssertionFailed result) | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | true with G.choose (now c) picked (privateState c)
  ...   | nothing = λ ()
  ...   | just d = λ { refl → q-retained refl }
  queue-step (selectPolicy picked) c | selecting | true | true | false = λ ()
  queue-step (selectPolicy picked) c | selecting | true | false | true = λ ()
  queue-step (selectPolicy picked) c | selecting | true | false | false = λ ()
  queue-step (selectPolicy picked) c | selecting | false | true | true = λ ()
  queue-step (selectPolicy picked) c | selecting | false | true | false = λ ()
  queue-step (selectPolicy picked) c | selecting | false | false | true = λ ()
  queue-step (selectPolicy picked) c | selecting | false | false | false = λ ()
  queue-step (selectPolicy picked) c | publishPublic | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c | sampleInputs | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c | prepareWait | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c | (cancelTimer selected) | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c | (apply selected) | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c | (publishView work) | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c | (traceDecision work) | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c | (launch work) | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c | (register j rest) | _ | _ | _ = λ ()
  queue-step (selectPolicy picked) c | (completionAssertionFailed result) | _ | _ | _ = λ ()
  queue-step registerWakeup c with pc c
  ... | prepareWait = λ { refl → q-retained refl }
  queue-step registerWakeup c | publishPublic = λ ()
  queue-step registerWakeup c | sampleInputs = λ ()
  queue-step registerWakeup c | selecting = λ ()
  queue-step registerWakeup c | (cancelTimer selected) = λ ()
  queue-step registerWakeup c | (apply selected) = λ ()
  queue-step registerWakeup c | (publishView work) = λ ()
  queue-step registerWakeup c | (traceDecision work) = λ ()
  queue-step registerWakeup c | (launch work) = λ ()
  queue-step registerWakeup c | (register j rest) = λ ()
  queue-step registerWakeup c | (completionAssertionFailed result) = λ ()
  queue-step expireWakeup c with pc c | wakeupAt c | wakeupReady c
  ... | selecting | just _ | false = λ { refl → q-retained refl }
  ... | selecting | just _ | true = λ ()
  ... | selecting | nothing | _ = λ ()
  queue-step expireWakeup c | publishPublic | _ | _ = λ ()
  queue-step expireWakeup c | sampleInputs | _ | _ = λ ()
  queue-step expireWakeup c | prepareWait | _ | _ = λ ()
  queue-step expireWakeup c | (cancelTimer selected) | _ | _ = λ ()
  queue-step expireWakeup c | (apply selected) | _ | _ = λ ()
  queue-step expireWakeup c | (publishView work) | _ | _ = λ ()
  queue-step expireWakeup c | (traceDecision work) | _ | _ = λ ()
  queue-step expireWakeup c | (launch work) | _ | _ = λ ()
  queue-step expireWakeup c | (register j rest) | _ | _ = λ ()
  queue-step expireWakeup c | (completionAssertionFailed result) | _ | _ = λ ()
  queue-step cancelWakeup c with pc c
  ... | cancelTimer selected = λ { refl → q-retained refl }
  queue-step cancelWakeup c | publishPublic = λ ()
  queue-step cancelWakeup c | sampleInputs = λ ()
  queue-step cancelWakeup c | prepareWait = λ ()
  queue-step cancelWakeup c | selecting = λ ()
  queue-step cancelWakeup c | (apply selected) = λ ()
  queue-step cancelWakeup c | (publishView work) = λ ()
  queue-step cancelWakeup c | (traceDecision work) = λ ()
  queue-step cancelWakeup c | (launch work) = λ ()
  queue-step cancelWakeup c | (register j rest) = λ ()
  queue-step cancelWakeup c | (completionAssertionFailed result) = λ ()
  queue-step selectWakeup c with pc c | noMonitor c | noCompletions c | noTargets c | wakeupReady c | wakeupAt c | G.firstReady (now c) (privateState c)
  ... | selecting | true | true | true | true | just deadline | nothing = λ { refl → q-retained refl }
  ... | selecting | false | _ | _ | _ | _ | _ = λ ()
  ... | selecting | true | false | _ | _ | _ | _ = λ ()
  ... | selecting | true | true | false | _ | _ | _ = λ ()
  ... | selecting | true | true | true | false | _ | _ = λ ()
  ... | selecting | true | true | true | true | nothing | _ = λ ()
  ... | selecting | true | true | true | true | just deadline | just ready = λ ()
  queue-step selectWakeup c | publishPublic | _ | _ | _ | _ | _ | _ = λ ()
  queue-step selectWakeup c | sampleInputs | _ | _ | _ | _ | _ | _ = λ ()
  queue-step selectWakeup c | prepareWait | _ | _ | _ | _ | _ | _ = λ ()
  queue-step selectWakeup c | (cancelTimer selected) | _ | _ | _ | _ | _ | _ = λ ()
  queue-step selectWakeup c | (apply selected) | _ | _ | _ | _ | _ | _ = λ ()
  queue-step selectWakeup c | (publishView work) | _ | _ | _ | _ | _ | _ = λ ()
  queue-step selectWakeup c | (traceDecision work) | _ | _ | _ | _ | _ | _ = λ ()
  queue-step selectWakeup c | (launch work) | _ | _ | _ | _ | _ | _ = λ ()
  queue-step selectWakeup c | (register j rest) | _ | _ | _ | _ | _ | _ = λ ()
  queue-step selectWakeup c | (completionAssertionFailed result) | _ | _ | _ | _ | _ | _ = λ ()
  queue-step (applyAt t) c with pc c | now c ≤? t
  ... | apply (policy d) | yes _ = λ { refl → q-retained refl }
  ... | apply (completion result) | yes _ with G.completionAssertion result (privateState c)
  ...   | false = λ { refl → q-retained refl }
  ...   | true = λ { refl → q-retained refl }
  queue-step (applyAt t) c | apply (monitor changes delay) | yes _ = λ { refl → q-retained refl }
  queue-step (applyAt t) c | apply (targets t′) | yes _ = λ { refl → q-retained refl }
  queue-step (applyAt t) c | apply (wakeup deadline) | yes _ with deadline ≤? t
  ...   | yes _ = λ { refl → q-retained refl }
  ...   | no _ = λ ()
  queue-step (applyAt t) c | apply (policy d) | no _ = λ ()
  queue-step (applyAt t) c | apply (completion result) | no _ = λ ()
  queue-step (applyAt t) c | apply (monitor changes delay) | no _ = λ ()
  queue-step (applyAt t) c | apply (targets t′) | no _ = λ ()
  queue-step (applyAt t) c | apply (wakeup deadline) | no _ = λ ()
  queue-step (applyAt t) c | publishPublic | _ = λ ()
  queue-step (applyAt t) c | sampleInputs | _ = λ ()
  queue-step (applyAt t) c | prepareWait | _ = λ ()
  queue-step (applyAt t) c | selecting | _ = λ ()
  queue-step (applyAt t) c | (cancelTimer selected) | _ = λ ()
  queue-step (applyAt t) c | (publishView work) | _ = λ ()
  queue-step (applyAt t) c | (traceDecision work) | _ = λ ()
  queue-step (applyAt t) c | (launch work) | _ = λ ()
  queue-step (applyAt t) c | (register j rest) | _ = λ ()
  queue-step (applyAt t) c | (completionAssertionFailed result) | _ = λ ()
  queue-step publishCounters c with pc c
  ... | publishView work = λ { refl → q-retained refl }
  queue-step publishCounters c | publishPublic = λ ()
  queue-step publishCounters c | sampleInputs = λ ()
  queue-step publishCounters c | prepareWait = λ ()
  queue-step publishCounters c | selecting = λ ()
  queue-step publishCounters c | (cancelTimer selected) = λ ()
  queue-step publishCounters c | (apply selected) = λ ()
  queue-step publishCounters c | (traceDecision work) = λ ()
  queue-step publishCounters c | (launch work) = λ ()
  queue-step publishCounters c | (register j rest) = λ ()
  queue-step publishCounters c | (completionAssertionFailed result) = λ ()
  queue-step traceSelection c with pc c
  ... | traceDecision work = λ { refl → q-retained refl }
  queue-step traceSelection c | publishPublic = λ ()
  queue-step traceSelection c | sampleInputs = λ ()
  queue-step traceSelection c | prepareWait = λ ()
  queue-step traceSelection c | selecting = λ ()
  queue-step traceSelection c | (cancelTimer selected) = λ ()
  queue-step traceSelection c | (apply selected) = λ ()
  queue-step traceSelection c | (publishView work) = λ ()
  queue-step traceSelection c | (launch work) = λ ()
  queue-step traceSelection c | (register j rest) = λ ()
  queue-step traceSelection c | (completionAssertionFailed result) = λ ()
  queue-step registerJob c with pc c
  ... | register j rest = λ { refl → q-retained refl }
  queue-step registerJob c | publishPublic = λ ()
  queue-step registerJob c | sampleInputs = λ ()
  queue-step registerJob c | prepareWait = λ ()
  queue-step registerJob c | selecting = λ ()
  queue-step registerJob c | (cancelTimer selected) = λ ()
  queue-step registerJob c | (apply selected) = λ ()
  queue-step registerJob c | (publishView work) = λ ()
  queue-step registerJob c | (traceDecision work) = λ ()
  queue-step registerJob c | (launch work) = λ ()
  queue-step registerJob c | (completionAssertionFailed result) = λ ()
  queue-step (forkJob caller child sock) c with pc c | workerFree caller c
  ... | launch [] | _ = λ ()
  ... | launch (work ∷ rest) | true = λ { refl → q-retained refl }
  ... | launch (work ∷ rest) | false = λ ()
  queue-step (forkJob caller child sock) c | publishPublic | _ = λ ()
  queue-step (forkJob caller child sock) c | sampleInputs | _ = λ ()
  queue-step (forkJob caller child sock) c | prepareWait | _ = λ ()
  queue-step (forkJob caller child sock) c | selecting | _ = λ ()
  queue-step (forkJob caller child sock) c | (cancelTimer selected) | _ = λ ()
  queue-step (forkJob caller child sock) c | (apply selected) | _ = λ ()
  queue-step (forkJob caller child sock) c | (publishView work) | _ = λ ()
  queue-step (forkJob caller child sock) c | (traceDecision work) | _ = λ ()
  queue-step (forkJob caller child sock) c | (register j rest) | _ = λ ()
  queue-step (forkJob caller child sock) c | (completionAssertionFailed result) | _ = λ ()
  queue-step finishLaunch c with pc c
  ... | launch [] = λ { refl → q-retained refl }
  ... | launch (work ∷ rest) = λ ()
  queue-step finishLaunch c | publishPublic = λ ()
  queue-step finishLaunch c | sampleInputs = λ ()
  queue-step finishLaunch c | prepareWait = λ ()
  queue-step finishLaunch c | selecting = λ ()
  queue-step finishLaunch c | (cancelTimer selected) = λ ()
  queue-step finishLaunch c | (apply selected) = λ ()
  queue-step finishLaunch c | (publishView work) = λ ()
  queue-step finishLaunch c | (traceDecision work) = λ ()
  queue-step finishLaunch c | (register j rest) = λ ()
  queue-step finishLaunch c | (completionAssertionFailed result) = λ ()
  queue-step (jobStep j action) c with lookup j (jobs c)
  ... | nothing = λ ()
  ... | just frame with queued frame | J.step action (execution frame) (world c) in stepped
  ...   | false | just (f′ , w′) = λ { refl → q-retained refl }
  ...   | true | _ = λ ()
  ...   | false | nothing = λ ()
  queue-step (enqueueCompletion j delay) c with lookup j (jobs c) in found
  ... | nothing = λ ()
  ... | just frame with queued frame | J.pc (execution frame) in completed
  ...   | false | J.complete result with validCompletionDelay (J.work (execution frame)) result delay
  ...     | false = λ ()
  ...     | true = λ { refl → q-appended j delay frame result found completed refl }
  queue-step (enqueueCompletion j delay) c | just frame | true | _ = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.begin = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.awaitAcquire = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | (J.startBundle t ns) = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | (J.publishBundle t) = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.markWarm = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.forkMonitor = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.finishActivation = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.awaitHot = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.awaitAll = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.callRelease = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.awaitRelease = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | J.delayFailure = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | (J.awaitCold result) = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | (J.acquirePolicy fault) = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | (J.nodeDelivery fault) = λ ()
  queue-step (enqueueCompletion j delay) c | just frame | false | (J.nodeRethrow fault) = λ ()
  queue-step (deregisterJob j) c with lookup j (jobs c)
  ... | nothing = λ ()
  ... | just frame with queued frame | deregistered frame | any (λ x → does (x ≟ j)) (pool c)
  ...   | true | true | true = λ ()
  ...   | true | true | false = λ ()
  ...   | true | false | true = λ { refl → q-retained refl }
  ...   | true | false | false = λ ()
  ...   | false | true | true = λ ()
  ...   | false | true | false = λ ()
  ...   | false | false | true = λ ()
  ...   | false | false | false = λ ()
  queue-step (protocolResult ref n result) c with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.step (P.protocolResult n result) peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , ig′) = λ { refl → q-retained refl }
  queue-step (publishInitiatorResult ref i) c with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.takePending i (P.pendingResults peer) | lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c)))))) in observed
  ...   | just ((n , result) , retained) | just observedMux with Life.muxAllowed (P.muxRef peer) Life.jobAccess (Inbound.handlerLifecycles (CM.core (J.cm (world c))))
  ...     | false = λ ()
  ...     | true = λ { refl → q-retained refl }
  queue-step (publishInitiatorResult ref i) c | just peer | nothing | _ = λ ()
  queue-step (publishInitiatorResult ref i) c | just peer | just selected | nothing = λ ()
  queue-step (observeInitiatorFailure ref) c with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
  ...   | nothing = λ ()
  ...   | just observedMux with M.completions observedMux
  ...     | M.jobResult M.initiatorJob n (errored err) ∷ rest with CM.advance
    (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c)) in stepped
  ...       | nothing = λ ()
  ...       | just cm′ = λ { refl → q-retained refl }
  queue-step (observeInitiatorFailure ref) c | just peer | just observedMux | [] = λ ()
  queue-step (observeInitiatorFailure ref) c | just peer | just observedMux | M.jobResult M.responderJob n outcome ∷ rest = λ ()
  queue-step (observeInitiatorFailure ref) c | just peer | just observedMux | M.jobResult M.initiatorJob n clean ∷ rest = λ ()
  queue-step (pollPeer ref caller) c with lookup ref (J.peers (world c)) | lookup ref (monitors c)
  ... | just peer | nothing with P.monitorStarted peer | P.status peer
  ...   | true | P.peerCooling with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...     | nothing = λ ()
  ...     | just (peer′ , _) = λ { refl → q-retained refl }
  queue-step (pollPeer ref caller) c | just peer | nothing | true | P.peerCold = λ { refl → q-retained refl }
  queue-step (pollPeer ref caller) c | just peer | nothing | true | P.peerWarm with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl → q-retained refl }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl → q-retained refl }
  queue-step (pollPeer ref caller) c | just peer | nothing | true | P.peerHot with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl → q-retained refl }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl → q-retained refl }
  queue-step (pollPeer ref caller) c | just peer | nothing | false | _ = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f with J.pc f
  ... | J.awaitCold _ with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , _) = λ { refl → q-retained refl }
  queue-step (pollPeer ref caller) c | just peer | just f | J.begin = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | J.awaitAcquire = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | (J.startBundle t ns) = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | (J.publishBundle t) = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | J.markWarm = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | J.forkMonitor = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | J.finishActivation = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | J.awaitHot = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | J.awaitAll = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | J.callRelease = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | J.awaitRelease = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | J.delayFailure = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | (J.complete result) = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | (J.acquirePolicy fault) = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | (J.nodeDelivery fault) = λ ()
  queue-step (pollPeer ref caller) c | just peer | just f | (J.nodeRethrow fault) = λ ()
  queue-step (pollPeer ref caller) c | nothing | _ = λ ()
  queue-step (monitorStep ref action) c with lookup ref (monitors c)
  ... | nothing = λ ()
  ... | just f with J.step action f (world c) in stepped
  ...   | nothing = λ ()
  ...   | just (f′ , w′) = λ { refl → q-retained refl }
  queue-step (monitorFinished ref) c with lookup ref (monitors c)
  ... | nothing = λ ()
  ... | just f with J.pc f
  ...   | J.complete _ = λ { refl → q-retained refl }
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

governor-source : ∀ a s {t} → GP.step (GP.run a) s ≡ just t →
  Σ Policy.State (λ source → GP.Production.step (Policy.dispatch a) (GP.source s) ≡ just source × GP.machine t ≡ Policy.machine source)
governor-source a s eq with GP.normalPool a s | GP.Production.step (Policy.dispatch a) (GP.source s) in moved
... | just p | just source with GP.noteReturn a (Policy.machine source) p
...   | just returned = case just-injective eq of λ { refl → source , refl , refl }
...   | nothing = case eq of λ ()
governor-source a s eq | nothing | _ = case eq of λ ()
governor-source a s eq | just _ | nothing = case eq of λ ()
publication-step : ∀ j delay s {t} → GP.step (GP.run (Sub.enqueueCompletion j delay)) s ≡ just t →
  Σ GP.Body (λ captured → lookup j (GP.Pool.handles (GP.pool s)) ≡ just (GP.Pool.bodyReturned captured) ×
    GP.returnedBody j (GP.machine s) captured ≡ true ×
    GP.Pool.step (GP.Pool.publishCompletion j) (GP.pool s) ≡ just (GP.pool t))
publication-step j delay s eq with lookup j (GP.Pool.handles (GP.pool s)) in found
... | just (GP.Pool.bodyReturned captured) with GP.returnedBody j (GP.machine s) captured in agrees
...   | false = case eq of λ ()
...   | true with GP.Production.step (Policy.dispatch (Sub.enqueueCompletion j delay)) (GP.source s)
...     | nothing rewrite found = case eq of λ ()
...     | just source rewrite found = case just-injective eq of λ { refl → captured , refl , agrees , refl }
publication-step j delay s eq | nothing = case eq of λ ()
publication-step j delay s eq | just GP.Pool.bodyRunning = case eq of λ ()
publication-step j delay s eq | just GP.Pool.bodyUnwinding = case eq of λ ()
publication-step j delay s eq | just (GP.Pool.deregisterPending _) = case eq of λ ()
publication-step j delay s eq | just (GP.Pool.deregistered _) = case eq of λ ()
publication-step j delay s eq | just (GP.Pool.resultAvailable _) = case eq of λ ()

payload-agreement : ∀ j c frame result payload → lookup j (Sub.jobs c) ≡ just frame →
 J.pc (Sub.execution frame) ≡ J.complete result → GP.returnedBody j c payload ≡ true →
 does (j ≟ GP.identity payload) ∧ GP.sameJob (J.work (Sub.execution frame)) (GP.work payload) ∧ GP.sameOutcome result (GP.outcome payload) ≡ true
payload-agreement j c frame result payload found completed agreed rewrite found | completed = agreed

-- Interpret each source queue effect under the real governor publication gate.
raw-change : ∀ a s t c → GP.step (GP.run a) s ≡ just t → GP.machine t ≡ c →
 Queue.QueueStep a (GP.machine s) c → Change (viewG s) (viewG t)
raw-change a s t c eq same (Queue.q-retained queues) = kept (trans (cong Sub.completions same) queues)
raw-change a s t c eq same (Queue.q-consumed result rest before after) = taken result rest before (trans (cong Sub.completions same) after)
raw-change .(Sub.enqueueCompletion j delay) s t c eq same (Queue.q-appended j delay frame result found completed queues)
 with publication-step j delay s eq
... | payload , returned , agreed , published = added (G.completion (J.work (Sub.execution frame)) result delay)
 (publication j frame payload found completed refl returned (payload-agreement j (GP.machine s) frame result payload found completed agreed))
 (trans (cong Sub.completions same) queues) published
run-change : ∀ a s {t} → GP.step (GP.run a) s ≡ just t → Change (viewG s) (viewG t)
run-change a s {t} eq with governor-source a s eq
... | source , stepped , same with GP.Production.step-projects (Policy.dispatch a) (GP.source s) stepped
... | Sub.next moved Sub.done = raw-change a s t (Policy.machine source) eq same (Queue.queue-step a (GP.machine s) moved)
restore-queue : ∀ f c → Sub.completions (GP.restoreCold f c) ≡ Sub.completions c
restore-queue f c with G.kind (J.work f) | J.pc f
... | G.establish | J.begin = refl
... | G.establish | J.complete result = refl
restore-queue f c | G.establish | J.awaitAcquire with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | (J.startBundle t ns) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | (J.publishBundle t) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | J.markWarm with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | J.forkMonitor with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | J.finishActivation with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | J.awaitHot with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | J.awaitAll with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | J.callRelease with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | J.awaitRelease with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | J.delayFailure with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | (J.awaitCold result) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | (J.acquirePolicy fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | (J.nodeDelivery fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.establish | (J.nodeRethrow fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-queue f c | G.forget | _ = refl
restore-queue f c | G.activate | _ = refl
restore-queue f c | G.close | _ = refl
restore-queue f c | G.deactivate | _ = refl


delivery-change : ∀ blocked err s {s′} → GP.deliver blocked err s ≡ just s′ → Change (viewG s) (viewG s′)
delivery-change blocked err s eq with Pool.phase (GP.pool s)
... | Pool.cancelPending j with lookup j (Sub.jobs (GP.machine s)) | Pool.step Pool.deliverCancel (GP.pool s) in delivered
...   | just jf | just p′ with Cancel.start (J.caller (Sub.execution jf)) err
    (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s)
...     | just (f , c′) = case just-injective eq of λ { refl → kept refl }
...     | nothing = case eq of λ ()
delivery-change blocked err s eq | Pool.cancelPending j | nothing | _ = case eq of λ ()
delivery-change blocked err s eq | Pool.cancelPending j | just jf | nothing = case eq of λ ()
delivery-change blocked err s eq | Pool.openPool = case eq of λ ()
delivery-change blocked err s eq | Pool.closing = case eq of λ ()
delivery-change blocked err s eq | Pool.closedPool = case eq of λ ()
delivery-change blocked err s eq | (Pool.joinPending k) = case eq of λ ()

governor-change : ∀ a s {t} → GP.step a s ≡ just t → Change (viewG s) (viewG t)
governor-change (GP.run a) s eq = run-change a s eq
governor-change (GP.handoff w) s eq with GP.region w s | lookup w (CM.acquiring (GP.cm s))
... | Cancel.forkedBeforeHandoff | just f with A.pc f
...   | A.connectedCommit _ _ _ = case just-injective eq of λ { refl → kept refl }
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | A.selecting = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.count next) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.allocatePromise e) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.openSocket e pid) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.configureSocket e pid) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.bindSocket e pid) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.connectSocket e pid) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.localAddress e pid) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.updateAddress e pid key) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.forkHandler e pid key) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.awaitResult e pid key) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.commitResult e key result) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.waitingInbound e key) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.closeError e err) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.removeError e err) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.complete result) = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | nothing = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.ordinary | _ = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.protectedCleanup | _ = case eq of λ ()
governor-change (GP.handoff w) s eq | Cancel.interruptibleOpen | _ = case eq of λ ()
governor-change (GP.beginClose order) s eq with Pool.step (Pool.beginClose order) (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → kept refl }
governor-change GP.requestCancel s eq with Pool.step Pool.requestCancel (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → kept refl }
governor-change GP.join s eq with Pool.step Pool.join (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → kept refl }
governor-change GP.finishClose s eq with Pool.step Pool.finishClose (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → kept refl }
governor-change (GP.publishAsyncResult j) s eq with Pool.step (Pool.publishAsyncResult j) (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → kept refl }
governor-change (GP.deliverCancellation err) s eq = delivery-change false err s eq
governor-change (GP.deliverOpenCancellation err) s eq = delivery-change true err s eq
governor-change (GP.cleanup j action) s eq with lookup j (GP.unwinding s)
... | nothing = case eq of λ ()
... | just f with Cancel.step action f (GP.cm s)
...   | nothing = case eq of λ ()
...   | just (f′ , c′) = case just-injective eq of λ { refl → kept refl }
governor-change (GP.bodyUnwound j) s eq with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
... | just f | just jf with Cancel.pc f
...   | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
...     | just p′ = case just-injective eq of λ { refl → kept (restore-queue (Sub.execution jf) (GP.machine s)) }
...     | nothing = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | just f | just jf | Cancel.finished Cancel.cleanupComplete with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
... | just p′ = case just-injective eq of λ { refl → kept (restore-queue (Sub.execution jf) (GP.machine s)) }
... | nothing = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | just f | just jf | Cancel.cleaning active = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | nothing | _ = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | just f | nothing = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with Pool.step (Pool.resumeAfterUnwindError j) (GP.pool s) in advanced
...     | just p′ = case just-injective eq of λ { refl → kept refl }
...     | nothing = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.cleaning active | _ | _ = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished Cancel.abandoned | _ | _ = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished Cancel.cleanupComplete | _ | _ = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.noCaller | _ = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.releasing active | _ = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.begin = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.startBundle t ns) = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.publishBundle t) = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.markWarm = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.forkMonitor = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.finishActivation = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitHot = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitAll = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.callRelease = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitRelease = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.delayFailure = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.awaitCold result) = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.complete result) = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.acquirePolicy fault) = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeDelivery fault) = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeRethrow fault) = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | nothing | _ = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq | just f | nothing = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq with lookup j (Sub.jobs (GP.machine s)) | Pool.step (Pool.deregister j) (GP.pool s) in advanced
... | just jf | just p′ with lookup j (Pool.handles (GP.pool s))
...   | just (Pool.deregisterPending Pool.cancelledExit) = case just-injective eq of λ { refl → kept refl }
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | nothing = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just Pool.bodyRunning = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.bodyReturned result) = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just Pool.bodyUnwinding = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.deregisterPending Pool.normalExit) = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.deregistered ex) = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.resultAvailable ex) = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | nothing | _ = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | nothing = case eq of λ ()


finish-view : ∀ clear ref s → view (PS.finishPeer clear ref s) ≡ view s
finish-view clear ref s with lookup ref (J.peers (Sub.world (PS.machine s)))
... | nothing = refl
... | just peer = refl
poll-view : ∀ ref before after → view (PS.notePoll ref before after) ≡ view after
poll-view ref before after with PS.byPeer ref (PS.monitors before) |
  lookup ref (J.peers (Sub.world (PS.machine before))) | lookup ref (J.peers (Sub.world (PS.machine after)))
... | just (tid , t) | just old | just next with Peer.monitorStarted next
...   | false = refl
...   | true = refl
poll-view ref before after | nothing | _ | _ = refl
poll-view ref before after | just (tid , t) | nothing | _ = refl
poll-view ref before after | just (tid , t) | just old | nothing = refl
note-view : ∀ action before after → view (PS.noteGovernor action before after) ≡ view after
note-view (GP.run (Sub.pollPeer ref w)) before after = poll-view ref before after
note-view (GP.run (Sub.core a)) before after = refl
note-view (GP.run Sub.publishPublicState) before after = refl
note-view (GP.run (Sub.sampleTime t)) before after = refl
note-view (GP.run (Sub.applyAt t)) before after = refl
note-view (GP.run (Sub.setTargets target)) before after = refl
note-view (GP.run (Sub.selectMonitor delay)) before after = refl
note-view (GP.run Sub.selectCompletion) before after = refl
note-view (GP.run Sub.selectTargets) before after = refl
note-view (GP.run Sub.selectWakeup) before after = refl
note-view (GP.run Sub.registerWakeup) before after = refl
note-view (GP.run Sub.expireWakeup) before after = refl
note-view (GP.run Sub.cancelWakeup) before after = refl
note-view (GP.run Sub.publishCounters) before after = refl
note-view (GP.run Sub.traceSelection) before after = refl
note-view (GP.run (Sub.selectPolicy picked)) before after = refl
note-view (GP.run (Sub.forkJob caller child sock)) before after = refl
note-view (GP.run Sub.registerJob) before after = refl
note-view (GP.run Sub.finishLaunch) before after = refl
note-view (GP.run (Sub.jobStep j a)) before after = refl
note-view (GP.run (Sub.enqueueCompletion j delay)) before after = refl
note-view (GP.run (Sub.deregisterJob j)) before after = refl
note-view (GP.run (Sub.protocolResult ref n result)) before after = refl
note-view (GP.run (Sub.publishInitiatorResult ref i)) before after = refl
note-view (GP.run (Sub.monitorStep ref a)) before after = refl
note-view (GP.run (Sub.monitorFinished ref)) before after = refl
note-view (GP.run (Sub.observeInitiatorFailure ref)) before after = refl
note-view (GP.handoff w) before after = refl
note-view (GP.beginClose order) before after = refl
note-view GP.requestCancel before after = refl
note-view GP.join before after = refl
note-view GP.finishClose before after = refl
note-view (GP.deliverCancellation err) before after = refl
note-view (GP.deliverOpenCancellation err) before after = refl
note-view (GP.cleanup j a) before after = refl
note-view (GP.bodyUnwound j) before after = refl
note-view (GP.recoverCloseFailure j) before after = refl
note-view (GP.deregisterCancelled j) before after = refl
note-view (GP.publishAsyncResult j) before after = refl

detach-view : ∀ err t s {f s′} → PS.detach err t s ≡ just (f , s′) → view s′ ≡ view s
detach-view err t s eq with lookup (PS.worker t) (CM.acquiring (PS.cm s))
... | just active = case eq of λ ()
... | nothing with lookup (PS.peerRef t) (Sub.monitors (PS.machine s))
...   | nothing with Cancel.start (PS.worker t) err Cancel.ordinary (PS.cm s)
...     | just (f , c′) = case just-injective eq of λ { refl → refl }
...     | nothing = case eq of λ ()
detach-view err t s eq | nothing | just follow with J.caller follow ≟ PS.worker t
... | no _ = case eq of λ ()
... | yes _ with Cancel.start (PS.worker t) err Cancel.ordinary (PS.cm s)
...   | nothing = case eq of λ ()
...   | just (f , c′) = case just-injective eq of λ { refl → refl }

-- A monitor fork's source step cannot enqueue or consume a completion.
job-queue : ∀ j a c {d} → Sub.advance (Sub.jobStep j a) c ≡ just d → Sub.completions d ≡ Sub.completions c
job-queue j a c eq with Queue.queue-step (Sub.jobStep j a) c eq
... | Queue.q-retained same = same
fork-change : ∀ j w s {s′} → PS.fork j w s ≡ just s′ → Change (view s) (view s′)
fork-change j (ident wid) s eq with lookup j (Sub.jobs (PS.machine s)) | PS.byParent j (PS.monitors s) | PS.freshWorker (ident wid) s
... | just jf | nothing | true with G.kind (J.work (Sub.execution jf)) |
  J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s)) |
  PS.byPeer (J.connectionRef (Sub.execution jf)) (PS.monitors s)
...   | G.establish | J.forkMonitor | true | nothing with
  Sub.advance (Sub.jobStep j J.launchMonitor) (PS.machine s) in spawned |
  BPool.step (BPool.forkConcurrent (ident wid)) (PS.monitorPool s) in forked
...     | just c′ | just p′ = case just-injective eq of λ { refl → kept (job-queue j J.launchMonitor (PS.machine s) spawned) }
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | nothing | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | just c′ | nothing = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.forget | _ | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.activate | _ | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.close | _ | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.deactivate | _ | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.begin | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitAcquire | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | (J.startBundle temp ns) | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | (J.publishBundle temp) | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.markWarm | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.finishActivation | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitHot | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitAll | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.callRelease | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitRelease | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.delayFailure | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | (J.awaitCold result) | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | (J.complete result) | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | (J.acquirePolicy fault) | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | (J.nodeDelivery fault) | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | (J.nodeRethrow fault) | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | false | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | true | just found = case eq of λ ()
fork-change j (ident wid) s eq | nothing | _ | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | just found | _ = case eq of λ ()
fork-change j (ident wid) s eq | just jf | nothing | false = case eq of λ ()

monitor-delivery-change : ∀ blocked err s {s′} → PS.deliverMonitor blocked err s ≡ just s′ → Change (view s) (view s′)
monitor-delivery-change blocked err s eq with BPool.phase (PS.monitorPool s)
... | BPool.cancelPending tid with lookup tid (PS.monitors s)
...   | nothing = case eq of λ ()
...   | just t with PS.monitorDeliverable blocked (PS.pc t) | BPool.step BPool.deliverCancel (PS.monitorPool s) in delivered
...     | true | just p′ with PS.detach err t s in detached
...       | just (f , s′) = case just-injective eq of λ { refl → kept (cong View.pending (detach-view err t s detached)) }
...       | nothing = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.cancelPending tid | just t | false | _ = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.cancelPending tid | just t | true | nothing = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.openPool = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.closing = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.closedPool = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.joinPending tid = case eq of λ ()

supervision-change : ∀ action s {s′} → PS.step action s ≡ just s′ → Change (view s) (view s′)
supervision-change (PS.run a) s eq with PS.governorAllowed a s
... | false = case eq of λ ()
... | true with GP.step a (PS.governor s) in stepped
...   | nothing = case eq of λ ()
...   | just g′ = case just-injective eq of λ { refl → right-view (sym (note-view a s (record s { governor = g′ }))) (governor-change a (PS.governor s) stepped) }
supervision-change (PS.forkMonitor j w) s eq = fork-change j w s eq
supervision-change (PS.registerMonitor tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.parentPC t | BPool.step (BPool.registerConcurrent tid) (PS.monitorPool s) in registered
...   | PS.created | just p′ = case just-injective eq of λ { refl → kept refl }
supervision-change (PS.registerMonitor tid) s eq | just t | PS.created | nothing = case eq of λ ()
supervision-change (PS.registerMonitor tid) s eq | just t | PS.registered | _ = case eq of λ ()
supervision-change (PS.registerMonitor tid) s eq | just t | PS.returned | _ = case eq of λ ()
supervision-change (PS.registerMonitor tid) s eq | nothing = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
... | just (tid , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s))
...   | PS.registered | J.forkMonitor | true = case just-injective eq of λ { refl → kept refl }
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.created | _ | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.returned | _ | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.begin | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitAcquire | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.startBundle temp ns) | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.publishBundle temp) | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.markWarm | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.finishActivation | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitHot | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitAll | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.callRelease | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitRelease | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.delayFailure | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.awaitCold result) | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.complete result) | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.acquirePolicy fault) | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.nodeDelivery fault) | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.nodeRethrow fault) | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.forkMonitor | false = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | nothing | _ = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq | just found | nothing = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
... | just (_ , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf)
...   | PS.returned | J.complete result with GPool.step
    (GPool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (PS.governor s)) in returned
...     | just p′ = case just-injective eq of λ { refl → kept refl }
...     | nothing = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.created | _ = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.registered | _ = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.begin = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitAcquire = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.startBundle temp ns) = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.publishBundle temp) = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.markWarm = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.forkMonitor = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.finishActivation = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitHot = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitAll = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.callRelease = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitRelease = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.delayFailure = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.awaitCold result) = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.acquirePolicy fault) = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.nodeDelivery fault) = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.nodeRethrow fault) = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | nothing | _ = case eq of λ ()
supervision-change (PS.finishEstablishment j) s eq | just found | nothing = case eq of λ ()
supervision-change (PS.monitorException tid err) s eq with lookup tid (PS.monitors s)
... | just t with PS.bodyActive tid t s | PS.detach err t s in detached
...   | true | just (f , s′) = case just-injective eq of λ { refl → kept (cong View.pending (detach-view err t s detached)) }
supervision-change (PS.monitorException tid err) s eq | just t | false | _ = case eq of λ ()
supervision-change (PS.monitorException tid err) s eq | just t | true | nothing = case eq of λ ()
supervision-change (PS.monitorException tid err) s eq | nothing = case eq of λ ()
supervision-change (PS.commitMonitorError tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t | lookup (PS.peerRef t) (J.peers (Sub.world (PS.machine s)))
...   | PS.errorWait err | just peer with Peer.demoted (Peer.key peer) (PS.shared s)
...     | true = case just-injective eq of λ { refl → kept refl }
...     | false = case eq of λ ()
supervision-change (PS.commitMonitorError tid) s eq | just t | PS.errorWait err | nothing = case eq of λ ()
supervision-change (PS.commitMonitorError tid) s eq | just t | PS.observing | _ = case eq of λ ()
supervision-change (PS.commitMonitorError tid) s eq | just t | PS.normalFinishing | _ = case eq of λ ()
supervision-change (PS.commitMonitorError tid) s eq | just t | PS.cancelling | _ = case eq of λ ()
supervision-change (PS.commitMonitorError tid) s eq | just t | PS.exited | _ = case eq of λ ()
supervision-change (PS.commitMonitorError tid) s eq | just t | (PS.errorFinishing err) | _ = case eq of λ ()
supervision-change (PS.commitMonitorError tid) s eq | nothing = case eq of λ ()
supervision-change (PS.finishMonitor tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t | BPool.step (BPool.bodyReturnedWith tid nothing) (PS.monitorPool s) in returned
...   | PS.normalFinishing | just p′ = case just-injective eq of λ { refl → kept (cong View.pending (finish-view true (PS.peerRef t) s)) }
supervision-change (PS.finishMonitor tid) s eq | just t | PS.normalFinishing | nothing = case eq of λ ()
supervision-change (PS.finishMonitor tid) s eq | just t | PS.observing | _ = case eq of λ ()
supervision-change (PS.finishMonitor tid) s eq | just t | PS.cancelling | _ = case eq of λ ()
supervision-change (PS.finishMonitor tid) s eq | just t | PS.exited | _ = case eq of λ ()
supervision-change (PS.finishMonitor tid) s eq | just t | (PS.errorWait err) | _ = case eq of λ ()
supervision-change (PS.finishMonitor tid) s eq | just t | (PS.errorFinishing err) | _ = case eq of λ ()
supervision-change (PS.finishMonitor tid) s eq | nothing = case eq of λ ()
supervision-change (PS.finishMonitorError tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t
...   | PS.errorFinishing err with BPool.step (BPool.bodyReturnedWith tid (just err)) (PS.monitorPool s) in returned
...     | just p′ = case just-injective eq of λ { refl → kept (cong View.pending (finish-view true (PS.peerRef t) s)) }
...     | nothing = case eq of λ ()
supervision-change (PS.finishMonitorError tid) s eq | just t | PS.observing = case eq of λ ()
supervision-change (PS.finishMonitorError tid) s eq | just t | PS.normalFinishing = case eq of λ ()
supervision-change (PS.finishMonitorError tid) s eq | just t | PS.cancelling = case eq of λ ()
supervision-change (PS.finishMonitorError tid) s eq | just t | PS.exited = case eq of λ ()
supervision-change (PS.finishMonitorError tid) s eq | just t | (PS.errorWait err) = case eq of λ ()
supervision-change (PS.finishMonitorError tid) s eq | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq with Scope.cursor (PS.scopes s) | GPool.parentFork (GP.pool (PS.governor s))
... | Scope.closing Scope.governor | just pending = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.openScope | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.churn | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.localRoot | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.ledger | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.governor | nothing with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.readyToFinish | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.finishedScope | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.beginUnwind) s eq with Scope.step (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.requestCancel) s eq with Scope.step (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.join) s eq with Scope.step (PS.governorPoolClosed s) Scope.join (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.finishClose) s eq with Scope.step (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope (Scope.beginFailure actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope (Scope.bodyExit actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope (Scope.publishResult actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.beginMonitorClose order) s eq with Scope.closed (PS.scopes s)
... | false = case eq of λ ()
... | true with BPool.step (BPool.beginClose order) (PS.monitorPool s) in advanced
...   | just p′ = case just-injective eq of λ { refl → kept refl }
...   | nothing = case eq of λ ()
supervision-change PS.requestMonitorCancel s eq with BPool.step BPool.requestCancel (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change PS.joinMonitor s eq with BPool.step BPool.join (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change PS.finishMonitorClose s eq with BPool.step BPool.finishClose (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.deregisterMonitor tid) s eq with BPool.step (BPool.deregister tid) (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.publishMonitorResult tid) s eq with BPool.step (BPool.publishAsyncResult tid) (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → kept refl }
... | nothing = case eq of λ ()
supervision-change (PS.deliverMonitorCancellation err) s eq = monitor-delivery-change false err s eq
supervision-change (PS.deliverBlockedMonitorCancellation err) s eq = monitor-delivery-change true err s eq
supervision-change (PS.monitorBodyUnwound tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t | PS.interrupted t
...   | PS.cancelling | just f with Cancel.pc f
...     | Cancel.finished Cancel.abandoned with BPool.step (BPool.bodyUnwound tid) (PS.monitorPool s) in advanced
...       | just p′ = case just-injective eq of λ { refl → kept (cong View.pending (finish-view false (PS.peerRef t) s)) }
...       | nothing = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | just f | Cancel.cleaning active = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | just f | Cancel.finished Cancel.cleanupComplete = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | just f | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | nothing = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | just t | PS.observing | _ = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | just t | PS.normalFinishing | _ = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | just t | PS.exited | _ = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | just t | (PS.errorWait err) | _ = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | just t | (PS.errorFinishing err) | _ = case eq of λ ()
supervision-change (PS.monitorBodyUnwound tid) s eq | nothing = case eq of λ ()

-- Reflect the existing boolean publication guard into exact typed identities.
and-left : ∀ {a b} → a ∧ b ≡ true → a ≡ true
and-left {true} eq = refl
and-left {false} ()
and-right : ∀ {a b} → a ∧ b ≡ true → b ≡ true
and-right {true} eq = eq
and-right {false} ()
dec-sound : ∀ {P : Set} (decision : Dec P) → does decision ≡ true → P
dec-sound (yes proof) eq = proof
dec-sound (no _) ()
same-capture : ∀ a b → GP.sameCapture a b ≡ true → a ≡ b
same-capture nothing nothing eq = refl
same-capture nothing (just _) ()
same-capture (just _) nothing ()
same-capture (just a) (just b) eq = cong just (dec-sound (a ≟ b) eq)
same-kind : ∀ a b → GP.sameKind a b ≡ true → a ≡ b
same-kind G.forget G.forget eq = refl
same-kind G.forget G.establish ()
same-kind G.forget G.activate ()
same-kind G.forget G.close ()
same-kind G.forget G.deactivate ()
same-kind G.establish G.forget ()
same-kind G.establish G.establish eq = refl
same-kind G.establish G.activate ()
same-kind G.establish G.close ()
same-kind G.establish G.deactivate ()
same-kind G.activate G.forget ()
same-kind G.activate G.establish ()
same-kind G.activate G.activate eq = refl
same-kind G.activate G.close ()
same-kind G.activate G.deactivate ()
same-kind G.close G.forget ()
same-kind G.close G.establish ()
same-kind G.close G.activate ()
same-kind G.close G.close eq = refl
same-kind G.close G.deactivate ()
same-kind G.deactivate G.forget ()
same-kind G.deactivate G.establish ()
same-kind G.deactivate G.activate ()
same-kind G.deactivate G.close ()
same-kind G.deactivate G.deactivate eq = refl
and-three : ∀ a b c → a ∧ b ∧ c ≡ true → a ≡ true × b ≡ true × c ≡ true
and-three true true true eq = refl , refl , refl
and-three true true false ()
and-three true false c ()
and-three false b c ()
same-work : ∀ a b → GP.sameJob a b ≡ true → a ≡ b
same-work (G.job k p capture) (G.job k′ p′ capture′) eq
 with and-three (GP.sameKind k k′) (does (p ≟ p′)) (GP.sameCapture capture capture′) eq
... | kinds , peers , captures rewrite same-kind k k′ kinds | dec-sound (p ≟ p′) peers | same-capture capture capture′ captures = refl
same-outcome : ∀ a b → GP.sameOutcome a b ≡ true → a ≡ b
same-outcome G.succeeded G.succeeded eq = refl
same-outcome G.succeeded G.failed ()
same-outcome G.succeeded G.demotionTimedOut ()
same-outcome G.succeeded (G.establishedOK ref′) ()
same-outcome G.failed G.succeeded ()
same-outcome G.failed G.failed eq = refl
same-outcome G.failed G.demotionTimedOut ()
same-outcome G.failed (G.establishedOK ref′) ()
same-outcome G.demotionTimedOut G.succeeded ()
same-outcome G.demotionTimedOut G.failed ()
same-outcome G.demotionTimedOut G.demotionTimedOut eq = refl
same-outcome G.demotionTimedOut (G.establishedOK ref′) ()
same-outcome (G.establishedOK ref) G.succeeded ()
same-outcome (G.establishedOK ref) G.failed ()
same-outcome (G.establishedOK ref) G.demotionTimedOut ()
same-outcome (G.establishedOK ref) (G.establishedOK ref′) eq = cong G.establishedOK (dec-sound (ref ≟ ref′) eq)
publication-agreement : ∀ v result (published : Publication v result) →
 GP.identity (Publication.payload published) ≡ Publication.job published ×
 GP.work (Publication.payload published) ≡ G.work result × GP.outcome (Publication.payload published) ≡ G.outcome result
publication-agreement v result published with and-three
 (does (Publication.job published ≟ GP.identity (Publication.payload published)))
 (GP.sameJob (G.work result) (GP.work (Publication.payload published)))
 (GP.sameOutcome (G.outcome result) (GP.outcome (Publication.payload published))) (Publication.agrees published)
... | identities , works , outcomes =
 sym (dec-sound (Publication.job published ≟ GP.identity (Publication.payload published)) identities) ,
 sym (same-work (G.work result) (GP.work (Publication.payload published)) works) ,
 sym (same-outcome (G.outcome result) (GP.outcome (Publication.payload published)) outcomes)
