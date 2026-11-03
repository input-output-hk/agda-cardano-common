{-# OPTIONS --guardedness #-}
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.PeerJobFrames (isIOManagerError : ErrorId → Bool) where
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
import Data.Empty
open import ConnectionManagement.Domain hiding (job)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Properties.GovernorCompletions as QueueFacts
private
 module PS = Supervision isIOManagerError
 module GP = PS.GP
 module Pool = GP.Pool
 module BPool = PS.Pool
 module GPool = GP.Pool
 module Q = QueueFacts isIOManagerError

-- Peer rows and CM retain the actual inputs to demotion and close operations.
record View : Set where
 constructor frameView
 field rows : Store JobId Sub.JobFrame
       peers : Peer.Runtime
       cm : CM.Configuration
raw : Sub.Configuration → View
raw c = frameView (Sub.jobs c) (J.peers (Sub.world c)) (J.cm (Sub.world c))
viewG : GP.State → View
viewG s = raw (GP.machine s)
view : PS.State → View
view s = viewG (PS.governor s)
data Tag : Set where
 other : Tag
 jobStep : JobId → J.Action → Tag
subTag : Sub.Action → Tag
subTag (Sub.jobStep j a) = jobStep j a
subTag _ = other
governorTag : GP.Action → Tag
governorTag (GP.run a) = subTag a
governorTag _ = other
supervisionTag : PS.Action → Tag
supervisionTag (PS.run a) = governorTag a
supervisionTag _ = other

-- Every stored execution is unchanged, born at begin, advanced by an actual
-- J.step, flagged without changing execution, or reset at an explicit adapter.
data Effect (tag : Tag) (before after : View) : Set where
 same : View.rows after ≡ View.rows before → Effect tag before after
 born : ∀ j next → J.pc (Sub.execution next) ≡ J.begin →
  View.rows after ≡ put j next (View.rows before) → Effect tag before after
 flags : ∀ j old next → lookup j (View.rows before) ≡ just old → Sub.execution next ≡ Sub.execution old →
  View.rows after ≡ put j next (View.rows before) → Effect tag before after
 tick : ∀ j a old next w w′ → lookup j (View.rows before) ≡ just old → J.peers w ≡ View.peers before → J.cm w ≡ View.cm before →
  J.step a (Sub.execution old) w ≡ just (next , w′) →
  View.rows after ≡ put j (record old { execution = next }) (View.rows before) →
  (tag ≡ jobStep j a) → Effect tag before after
 established : ∀ j old next → lookup j (View.rows before) ≡ just old → J.pc (Sub.execution old) ≡ J.forkMonitor →
  J.work (Sub.execution next) ≡ J.work (Sub.execution old) →
  View.rows after ≡ put j next (View.rows before) → Effect tag before after
 failed : ∀ j old next → lookup j (View.rows before) ≡ just old →
  Sub.execution next ≡ record (Sub.execution old) { pc = J.awaitCold G.failed } →
  View.rows after ≡ put j next (View.rows before) → Effect tag before after
after-rows : ∀ {tag before after next} → View.rows after ≡ View.rows next → Effect tag before after → Effect tag before next
after-rows sameRows (same eq) = same (trans (sym sameRows) eq)
after-rows sameRows (born j next pc eq) = born j next pc (trans (sym sameRows) eq)
after-rows sameRows (flags j old next found exec eq) = flags j old next found exec (trans (sym sameRows) eq)
after-rows sameRows (tick j a old next w w′ found peers shared stepped eq allowed) = tick j a old next w w′ found peers shared stepped (trans (sym sameRows) eq) allowed
after-rows sameRows (established j old next found pc work eq) = established j old next found pc work (trans (sym sameRows) eq)
after-rows sameRows (failed j old next found exec eq) = failed j old next found exec (trans (sym sameRows) eq)

module Raw where
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

  classify : ∀ a c {d} → advance a c ≡ just d → Effect (subTag a) (raw c) (raw d)
  classify (core action) c with CM.advance action (J.cm (world c)) in stepped
  ... | nothing = λ ()
  ... | just cm′ = λ { refl → same refl }
  classify publishPublicState c with pc c
  ... | publishPublic = λ { refl → same refl }
  classify publishPublicState c | sampleInputs = λ ()
  classify publishPublicState c | prepareWait = λ ()
  classify publishPublicState c | selecting = λ ()
  classify publishPublicState c | (cancelTimer selected) = λ ()
  classify publishPublicState c | (apply selected) = λ ()
  classify publishPublicState c | (publishView work) = λ ()
  classify publishPublicState c | (traceDecision work) = λ ()
  classify publishPublicState c | (launch work) = λ ()
  classify publishPublicState c | (register j rest) = λ ()
  classify publishPublicState c | (completionAssertionFailed result) = λ ()
  classify (sampleTime t) c with pc c | now c ≤? t
  ... | sampleInputs | yes _ = λ { refl → same refl }
  ... | sampleInputs | no _ = λ ()
  classify (sampleTime t) c | publishPublic | _ = λ ()
  classify (sampleTime t) c | prepareWait | _ = λ ()
  classify (sampleTime t) c | selecting | _ = λ ()
  classify (sampleTime t) c | (cancelTimer selected) | _ = λ ()
  classify (sampleTime t) c | (apply selected) | _ = λ ()
  classify (sampleTime t) c | (publishView work) | _ = λ ()
  classify (sampleTime t) c | (traceDecision work) | _ = λ ()
  classify (sampleTime t) c | (launch work) | _ = λ ()
  classify (sampleTime t) c | (register j rest) | _ = λ ()
  classify (sampleTime t) c | (completionAssertionFailed result) | _ = λ ()
  -- Target-input writes leave the stored job frames unchanged.
  classify (setTargets t) c = λ { refl → same refl }
  classify (selectMonitor delay) c with pc c | G.monitored (J.peers (world c)) (privateState c)
  ... | selecting | changes@(_ ∷ _) with completeDelays changes delay
  ...   | false = λ ()
  ...   | true = λ { refl → same refl }
  classify (selectMonitor delay) c | selecting | [] = λ ()
  classify (selectMonitor delay) c | publishPublic | _ = λ ()
  classify (selectMonitor delay) c | sampleInputs | _ = λ ()
  classify (selectMonitor delay) c | prepareWait | _ = λ ()
  classify (selectMonitor delay) c | (cancelTimer selected) | _ = λ ()
  classify (selectMonitor delay) c | (apply selected) | _ = λ ()
  classify (selectMonitor delay) c | (publishView work) | _ = λ ()
  classify (selectMonitor delay) c | (traceDecision work) | _ = λ ()
  classify (selectMonitor delay) c | (launch work) | _ = λ ()
  classify (selectMonitor delay) c | (register j rest) | _ = λ ()
  classify (selectMonitor delay) c | (completionAssertionFailed result) | _ = λ ()
  classify selectCompletion c with pc c | noMonitor c | completions c in fifo
  ... | selecting | true | x ∷ xs = λ { refl → same refl }
  ... | selecting | true | [] = λ ()
  ... | selecting | false | _ = λ ()
  classify selectCompletion c | publishPublic | _ | _ = λ ()
  classify selectCompletion c | sampleInputs | _ | _ = λ ()
  classify selectCompletion c | prepareWait | _ | _ = λ ()
  classify selectCompletion c | (cancelTimer selected) | _ | _ = λ ()
  classify selectCompletion c | (apply selected) | _ | _ = λ ()
  classify selectCompletion c | (publishView work) | _ | _ = λ ()
  classify selectCompletion c | (traceDecision work) | _ | _ = λ ()
  classify selectCompletion c | (launch work) | _ | _ = λ ()
  classify selectCompletion c | (register j rest) | _ | _ = λ ()
  classify selectCompletion c | (completionAssertionFailed result) | _ | _ = λ ()
  classify selectTargets c with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | false = λ { refl → same refl }
  classify selectTargets c | selecting | true | true | true = λ ()
  classify selectTargets c | selecting | true | false | true = λ ()
  classify selectTargets c | selecting | true | false | false = λ ()
  classify selectTargets c | selecting | false | true | true = λ ()
  classify selectTargets c | selecting | false | true | false = λ ()
  classify selectTargets c | selecting | false | false | true = λ ()
  classify selectTargets c | selecting | false | false | false = λ ()
  classify selectTargets c | publishPublic | _ | _ | _ = λ ()
  classify selectTargets c | sampleInputs | _ | _ | _ = λ ()
  classify selectTargets c | prepareWait | _ | _ | _ = λ ()
  classify selectTargets c | (cancelTimer selected) | _ | _ | _ = λ ()
  classify selectTargets c | (apply selected) | _ | _ | _ = λ ()
  classify selectTargets c | (publishView work) | _ | _ | _ = λ ()
  classify selectTargets c | (traceDecision work) | _ | _ | _ = λ ()
  classify selectTargets c | (launch work) | _ | _ | _ = λ ()
  classify selectTargets c | (register j rest) | _ | _ | _ = λ ()
  classify selectTargets c | (completionAssertionFailed result) | _ | _ | _ = λ ()
  classify (selectPolicy picked) c with pc c | noMonitor c | noCompletions c | noTargets c
  ... | selecting | true | true | true with G.choose (now c) picked (privateState c)
  ...   | nothing = λ ()
  ...   | just d = λ { refl → same refl }
  classify (selectPolicy picked) c | selecting | true | true | false = λ ()
  classify (selectPolicy picked) c | selecting | true | false | true = λ ()
  classify (selectPolicy picked) c | selecting | true | false | false = λ ()
  classify (selectPolicy picked) c | selecting | false | true | true = λ ()
  classify (selectPolicy picked) c | selecting | false | true | false = λ ()
  classify (selectPolicy picked) c | selecting | false | false | true = λ ()
  classify (selectPolicy picked) c | selecting | false | false | false = λ ()
  classify (selectPolicy picked) c | publishPublic | _ | _ | _ = λ ()
  classify (selectPolicy picked) c | sampleInputs | _ | _ | _ = λ ()
  classify (selectPolicy picked) c | prepareWait | _ | _ | _ = λ ()
  classify (selectPolicy picked) c | (cancelTimer selected) | _ | _ | _ = λ ()
  classify (selectPolicy picked) c | (apply selected) | _ | _ | _ = λ ()
  classify (selectPolicy picked) c | (publishView work) | _ | _ | _ = λ ()
  classify (selectPolicy picked) c | (traceDecision work) | _ | _ | _ = λ ()
  classify (selectPolicy picked) c | (launch work) | _ | _ | _ = λ ()
  classify (selectPolicy picked) c | (register j rest) | _ | _ | _ = λ ()
  classify (selectPolicy picked) c | (completionAssertionFailed result) | _ | _ | _ = λ ()
  classify registerWakeup c with pc c
  ... | prepareWait = λ { refl → same refl }
  classify registerWakeup c | publishPublic = λ ()
  classify registerWakeup c | sampleInputs = λ ()
  classify registerWakeup c | selecting = λ ()
  classify registerWakeup c | (cancelTimer selected) = λ ()
  classify registerWakeup c | (apply selected) = λ ()
  classify registerWakeup c | (publishView work) = λ ()
  classify registerWakeup c | (traceDecision work) = λ ()
  classify registerWakeup c | (launch work) = λ ()
  classify registerWakeup c | (register j rest) = λ ()
  classify registerWakeup c | (completionAssertionFailed result) = λ ()
  classify expireWakeup c with pc c | wakeupAt c | wakeupReady c
  ... | selecting | just _ | false = λ { refl → same refl }
  ... | selecting | just _ | true = λ ()
  ... | selecting | nothing | _ = λ ()
  classify expireWakeup c | publishPublic | _ | _ = λ ()
  classify expireWakeup c | sampleInputs | _ | _ = λ ()
  classify expireWakeup c | prepareWait | _ | _ = λ ()
  classify expireWakeup c | (cancelTimer selected) | _ | _ = λ ()
  classify expireWakeup c | (apply selected) | _ | _ = λ ()
  classify expireWakeup c | (publishView work) | _ | _ = λ ()
  classify expireWakeup c | (traceDecision work) | _ | _ = λ ()
  classify expireWakeup c | (launch work) | _ | _ = λ ()
  classify expireWakeup c | (register j rest) | _ | _ = λ ()
  classify expireWakeup c | (completionAssertionFailed result) | _ | _ = λ ()
  classify cancelWakeup c with pc c
  ... | cancelTimer selected = λ { refl → same refl }
  classify cancelWakeup c | publishPublic = λ ()
  classify cancelWakeup c | sampleInputs = λ ()
  classify cancelWakeup c | prepareWait = λ ()
  classify cancelWakeup c | selecting = λ ()
  classify cancelWakeup c | (apply selected) = λ ()
  classify cancelWakeup c | (publishView work) = λ ()
  classify cancelWakeup c | (traceDecision work) = λ ()
  classify cancelWakeup c | (launch work) = λ ()
  classify cancelWakeup c | (register j rest) = λ ()
  classify cancelWakeup c | (completionAssertionFailed result) = λ ()
  classify selectWakeup c with pc c | noMonitor c | noCompletions c | noTargets c | wakeupReady c | wakeupAt c | G.firstReady (now c) (privateState c)
  ... | selecting | true | true | true | true | just deadline | nothing = λ { refl → same refl }
  ... | selecting | false | _ | _ | _ | _ | _ = λ ()
  ... | selecting | true | false | _ | _ | _ | _ = λ ()
  ... | selecting | true | true | false | _ | _ | _ = λ ()
  ... | selecting | true | true | true | false | _ | _ = λ ()
  ... | selecting | true | true | true | true | nothing | _ = λ ()
  ... | selecting | true | true | true | true | just deadline | just ready = λ ()
  classify selectWakeup c | publishPublic | _ | _ | _ | _ | _ | _ = λ ()
  classify selectWakeup c | sampleInputs | _ | _ | _ | _ | _ | _ = λ ()
  classify selectWakeup c | prepareWait | _ | _ | _ | _ | _ | _ = λ ()
  classify selectWakeup c | (cancelTimer selected) | _ | _ | _ | _ | _ | _ = λ ()
  classify selectWakeup c | (apply selected) | _ | _ | _ | _ | _ | _ = λ ()
  classify selectWakeup c | (publishView work) | _ | _ | _ | _ | _ | _ = λ ()
  classify selectWakeup c | (traceDecision work) | _ | _ | _ | _ | _ | _ = λ ()
  classify selectWakeup c | (launch work) | _ | _ | _ | _ | _ | _ = λ ()
  classify selectWakeup c | (register j rest) | _ | _ | _ | _ | _ | _ = λ ()
  classify selectWakeup c | (completionAssertionFailed result) | _ | _ | _ | _ | _ | _ = λ ()
  classify (applyAt t) c with pc c | now c ≤? t
  ... | apply (policy d) | yes _ = λ { refl → same refl }
  ... | apply (completion result) | yes _ with G.completionAssertion result (privateState c)
  ...   | false = λ { refl → same refl }
  ...   | true = λ { refl → same refl }
  classify (applyAt t) c | apply (monitor changes delay) | yes _ = λ { refl → same refl }
  classify (applyAt t) c | apply (targets t′) | yes _ = λ { refl → same refl }
  classify (applyAt t) c | apply (wakeup deadline) | yes _ with deadline ≤? t
  ...   | yes _ = λ { refl → same refl }
  ...   | no _ = λ ()
  classify (applyAt t) c | apply (policy d) | no _ = λ ()
  classify (applyAt t) c | apply (completion result) | no _ = λ ()
  classify (applyAt t) c | apply (monitor changes delay) | no _ = λ ()
  classify (applyAt t) c | apply (targets t′) | no _ = λ ()
  classify (applyAt t) c | apply (wakeup deadline) | no _ = λ ()
  classify (applyAt t) c | publishPublic | _ = λ ()
  classify (applyAt t) c | sampleInputs | _ = λ ()
  classify (applyAt t) c | prepareWait | _ = λ ()
  classify (applyAt t) c | selecting | _ = λ ()
  classify (applyAt t) c | (cancelTimer selected) | _ = λ ()
  classify (applyAt t) c | (publishView work) | _ = λ ()
  classify (applyAt t) c | (traceDecision work) | _ = λ ()
  classify (applyAt t) c | (launch work) | _ = λ ()
  classify (applyAt t) c | (register j rest) | _ = λ ()
  classify (applyAt t) c | (completionAssertionFailed result) | _ = λ ()
  classify publishCounters c with pc c
  ... | publishView work = λ { refl → same refl }
  classify publishCounters c | publishPublic = λ ()
  classify publishCounters c | sampleInputs = λ ()
  classify publishCounters c | prepareWait = λ ()
  classify publishCounters c | selecting = λ ()
  classify publishCounters c | (cancelTimer selected) = λ ()
  classify publishCounters c | (apply selected) = λ ()
  classify publishCounters c | (traceDecision work) = λ ()
  classify publishCounters c | (launch work) = λ ()
  classify publishCounters c | (register j rest) = λ ()
  classify publishCounters c | (completionAssertionFailed result) = λ ()
  classify traceSelection c with pc c
  ... | traceDecision work = λ { refl → same refl }
  classify traceSelection c | publishPublic = λ ()
  classify traceSelection c | sampleInputs = λ ()
  classify traceSelection c | prepareWait = λ ()
  classify traceSelection c | selecting = λ ()
  classify traceSelection c | (cancelTimer selected) = λ ()
  classify traceSelection c | (apply selected) = λ ()
  classify traceSelection c | (publishView work) = λ ()
  classify traceSelection c | (launch work) = λ ()
  classify traceSelection c | (register j rest) = λ ()
  classify traceSelection c | (completionAssertionFailed result) = λ ()
  classify registerJob c with pc c
  ... | register j rest = λ { refl → same refl }
  classify registerJob c | publishPublic = λ ()
  classify registerJob c | sampleInputs = λ ()
  classify registerJob c | prepareWait = λ ()
  classify registerJob c | selecting = λ ()
  classify registerJob c | (cancelTimer selected) = λ ()
  classify registerJob c | (apply selected) = λ ()
  classify registerJob c | (publishView work) = λ ()
  classify registerJob c | (traceDecision work) = λ ()
  classify registerJob c | (launch work) = λ ()
  classify registerJob c | (completionAssertionFailed result) = λ ()
  classify (forkJob caller child sock) c with pc c | workerFree caller c
  ... | launch [] | _ = λ ()
  ... | launch (work ∷ rest) | true with G.captured work
  ...   | nothing = λ { refl → born (ident (nextJob c)) (jobFrame (J.frame work caller child sock (ident (nextPeer c)) J.begin) false false) refl refl }
  ...   | just ref = λ { refl → born (ident (nextJob c)) (jobFrame (J.frame work caller child sock ref J.begin) false false) refl refl }
  classify (forkJob caller child sock) c | launch (work ∷ rest) | false = λ ()
  classify (forkJob caller child sock) c | publishPublic | _ = λ ()
  classify (forkJob caller child sock) c | sampleInputs | _ = λ ()
  classify (forkJob caller child sock) c | prepareWait | _ = λ ()
  classify (forkJob caller child sock) c | selecting | _ = λ ()
  classify (forkJob caller child sock) c | (cancelTimer selected) | _ = λ ()
  classify (forkJob caller child sock) c | (apply selected) | _ = λ ()
  classify (forkJob caller child sock) c | (publishView work) | _ = λ ()
  classify (forkJob caller child sock) c | (traceDecision work) | _ = λ ()
  classify (forkJob caller child sock) c | (register j rest) | _ = λ ()
  classify (forkJob caller child sock) c | (completionAssertionFailed result) | _ = λ ()
  classify finishLaunch c with pc c
  ... | launch [] = λ { refl → same refl }
  ... | launch (work ∷ rest) = λ ()
  classify finishLaunch c | publishPublic = λ ()
  classify finishLaunch c | sampleInputs = λ ()
  classify finishLaunch c | prepareWait = λ ()
  classify finishLaunch c | selecting = λ ()
  classify finishLaunch c | (cancelTimer selected) = λ ()
  classify finishLaunch c | (apply selected) = λ ()
  classify finishLaunch c | (publishView work) = λ ()
  classify finishLaunch c | (traceDecision work) = λ ()
  classify finishLaunch c | (register j rest) = λ ()
  classify finishLaunch c | (completionAssertionFailed result) = λ ()
  classify (jobStep j action) c with lookup j (jobs c) in found
  ... | nothing = λ ()
  ... | just frame with queued frame | J.step action (execution frame) (world c) in stepped
  ...   | false | just (f′ , w′) = λ { refl → tick j action frame f′ (world c) w′ found refl refl stepped refl refl }
  ...   | true | _ = λ ()
  ...   | false | nothing = λ ()
  classify (enqueueCompletion j delay) c with lookup j (jobs c) in found
  ... | nothing = λ ()
  ... | just frame with queued frame | J.pc (execution frame) in completed
  ...   | false | J.complete result with validCompletionDelay (J.work (execution frame)) result delay
  ...     | false = λ ()
  ...     | true = λ { refl → flags j frame (record frame { queued = true }) found refl refl }
  classify (enqueueCompletion j delay) c | just frame | true | _ = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.begin = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.awaitAcquire = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | (J.startBundle t ns) = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | (J.publishBundle t) = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.markWarm = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.forkMonitor = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.finishActivation = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.awaitHot = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.awaitAll = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.callRelease = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.awaitRelease = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | J.delayFailure = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | (J.awaitCold result) = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | (J.acquirePolicy fault) = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | (J.nodeDelivery fault) = λ ()
  classify (enqueueCompletion j delay) c | just frame | false | (J.nodeRethrow fault) = λ ()
  classify (deregisterJob j) c with lookup j (jobs c) in found
  ... | nothing = λ ()
  ... | just frame with queued frame | deregistered frame | any (λ x → does (x ≟ j)) (pool c)
  ...   | true | true | true = λ ()
  ...   | true | true | false = λ ()
  ...   | true | false | true = λ { refl → flags j frame (record frame { deregistered = true }) found refl refl }
  ...   | true | false | false = λ ()
  ...   | false | true | true = λ ()
  ...   | false | true | false = λ ()
  ...   | false | false | true = λ ()
  ...   | false | false | false = λ ()
  classify (protocolResult ref n result) c with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.step (P.protocolResult n result) peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , ig′) = λ { refl → same refl }
  classify (publishInitiatorResult ref i) c with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with P.takePending i (P.pendingResults peer) | lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c)))))) in observed
  ...   | just ((n , result) , retained) | just observedMux with Life.muxAllowed (P.muxRef peer) Life.jobAccess (Inbound.handlerLifecycles (CM.core (J.cm (world c))))
  ...     | false = λ ()
  ...     | true = λ { refl → same refl }
  classify (publishInitiatorResult ref i) c | just peer | nothing | _ = λ ()
  classify (publishInitiatorResult ref i) c | just peer | just selected | nothing = λ ()
  classify (observeInitiatorFailure ref) c with lookup ref (J.peers (world c))
  ... | nothing = λ ()
  ... | just peer with lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
  ...   | nothing = λ ()
  ...   | just observedMux with M.completions observedMux
  ...     | M.jobResult M.initiatorJob n (errored err) ∷ rest with CM.advance
    (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c)) in stepped
  ...       | nothing = λ ()
  ...       | just cm′ = λ { refl → same refl }
  classify (observeInitiatorFailure ref) c | just peer | just observedMux | [] = λ ()
  classify (observeInitiatorFailure ref) c | just peer | just observedMux | M.jobResult M.responderJob n outcome ∷ rest = λ ()
  classify (observeInitiatorFailure ref) c | just peer | just observedMux | M.jobResult M.initiatorJob n clean ∷ rest = λ ()
  classify (pollPeer ref caller) c with lookup ref (J.peers (world c)) | lookup ref (monitors c)
  ... | just peer | nothing with P.monitorStarted peer | P.status peer
  ...   | true | P.peerCooling with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...     | nothing = λ ()
  ...     | just (peer′ , _) = λ { refl → same refl }
  classify (pollPeer ref caller) c | just peer | nothing | true | P.peerCold = λ { refl → same refl }
  classify (pollPeer ref caller) c | just peer | nothing | true | P.peerWarm with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl → same refl }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl → same refl }
  classify (pollPeer ref caller) c | just peer | nothing | true | P.peerHot with firstResult peer
  ... | nothing = λ ()
  ... | just (_ , errored _) = λ { refl → same refl }
  ... | just (kind , clean) with workerFree caller c
  ...   | false = λ ()
  ...   | true = λ { refl → same refl }
  classify (pollPeer ref caller) c | just peer | nothing | false | _ = λ ()
  classify (pollPeer ref caller) c | just peer | just f with J.pc f
  ... | J.awaitCold _ with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
  ...   | nothing = λ ()
  ...   | just (peer′ , _) = λ { refl → same refl }
  classify (pollPeer ref caller) c | just peer | just f | J.begin = λ ()
  classify (pollPeer ref caller) c | just peer | just f | J.awaitAcquire = λ ()
  classify (pollPeer ref caller) c | just peer | just f | (J.startBundle t ns) = λ ()
  classify (pollPeer ref caller) c | just peer | just f | (J.publishBundle t) = λ ()
  classify (pollPeer ref caller) c | just peer | just f | J.markWarm = λ ()
  classify (pollPeer ref caller) c | just peer | just f | J.forkMonitor = λ ()
  classify (pollPeer ref caller) c | just peer | just f | J.finishActivation = λ ()
  classify (pollPeer ref caller) c | just peer | just f | J.awaitHot = λ ()
  classify (pollPeer ref caller) c | just peer | just f | J.awaitAll = λ ()
  classify (pollPeer ref caller) c | just peer | just f | J.callRelease = λ ()
  classify (pollPeer ref caller) c | just peer | just f | J.awaitRelease = λ ()
  classify (pollPeer ref caller) c | just peer | just f | J.delayFailure = λ ()
  classify (pollPeer ref caller) c | just peer | just f | (J.complete result) = λ ()
  classify (pollPeer ref caller) c | just peer | just f | (J.acquirePolicy fault) = λ ()
  classify (pollPeer ref caller) c | just peer | just f | (J.nodeDelivery fault) = λ ()
  classify (pollPeer ref caller) c | just peer | just f | (J.nodeRethrow fault) = λ ()
  classify (pollPeer ref caller) c | nothing | _ = λ ()
  classify (monitorStep ref action) c with lookup ref (monitors c)
  ... | nothing = λ ()
  ... | just f with J.step action f (world c) in stepped
  ...   | nothing = λ ()
  ...   | just (f′ , w′) = λ { refl → same refl }
  classify (monitorFinished ref) c with lookup ref (monitors c)
  ... | nothing = λ ()
  ... | just f with J.pc f
  ...   | J.complete _ = λ { refl → same refl }
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

run-frames : ∀ a s {t} → GP.step (GP.run a) s ≡ just t → Effect (subTag a) (viewG s) (viewG t)
run-frames a s eq with Q.governor-source a s eq
... | source , advanced , sameMachine with GP.Production.step-projects (Policy.dispatch a) (GP.source s) advanced
... | Sub.next stepped Sub.done = after-rows (cong Sub.jobs (sym sameMachine)) (Raw.classify a (GP.machine s) stepped)
restore-frames : ∀ f c → Sub.jobs (GP.restoreCold f c) ≡ Sub.jobs c
restore-frames f c with G.kind (J.work f) | J.pc f
... | G.establish | J.begin = refl
... | G.establish | J.complete result = refl
restore-frames f c | G.establish | J.awaitAcquire with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | (J.startBundle t ns) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | (J.publishBundle t) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | J.markWarm with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | J.forkMonitor with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | J.finishActivation with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | J.awaitHot with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | J.awaitAll with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | J.callRelease with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | J.awaitRelease with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | J.delayFailure with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | (J.awaitCold result) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | (J.acquirePolicy fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | (J.nodeDelivery fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.establish | (J.nodeRethrow fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-frames f c | G.forget | _ = refl
restore-frames f c | G.activate | _ = refl
restore-frames f c | G.close | _ = refl
restore-frames f c | G.deactivate | _ = refl


delivery-change : ∀ blocked err s {s′} → GP.deliver blocked err s ≡ just s′ → Effect other (viewG s) (viewG s′)
delivery-change blocked err s eq with Pool.phase (GP.pool s)
... | Pool.cancelPending j with lookup j (Sub.jobs (GP.machine s)) | Pool.step Pool.deliverCancel (GP.pool s) in delivered
...   | just jf | just p′ with Cancel.start (J.caller (Sub.execution jf)) err
    (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s)
...     | just (f , c′) = case just-injective eq of λ { refl → same refl }
...     | nothing = case eq of λ ()
delivery-change blocked err s eq | Pool.cancelPending j | nothing | _ = case eq of λ ()
delivery-change blocked err s eq | Pool.cancelPending j | just jf | nothing = case eq of λ ()
delivery-change blocked err s eq | Pool.openPool = case eq of λ ()
delivery-change blocked err s eq | Pool.closing = case eq of λ ()
delivery-change blocked err s eq | Pool.closedPool = case eq of λ ()
delivery-change blocked err s eq | (Pool.joinPending k) = case eq of λ ()

governor-change : ∀ a s {t} → GP.step a s ≡ just t → Effect (governorTag a) (viewG s) (viewG t)
governor-change (GP.run a) s eq = run-frames a s eq
governor-change (GP.handoff w) s eq with GP.region w s | lookup w (CM.acquiring (GP.cm s))
... | Cancel.forkedBeforeHandoff | just f with A.pc f
...   | A.connectedCommit _ _ _ = case just-injective eq of λ { refl → same refl }
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
... | just p′ = case just-injective eq of λ { refl → same refl }
governor-change GP.requestCancel s eq with Pool.step Pool.requestCancel (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → same refl }
governor-change GP.join s eq with Pool.step Pool.join (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → same refl }
governor-change GP.finishClose s eq with Pool.step Pool.finishClose (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → same refl }
governor-change (GP.publishAsyncResult j) s eq with Pool.step (Pool.publishAsyncResult j) (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → same refl }
governor-change (GP.deliverCancellation err) s eq = delivery-change false err s eq
governor-change (GP.deliverOpenCancellation err) s eq = delivery-change true err s eq
governor-change (GP.cleanup j action) s eq with lookup j (GP.unwinding s)
... | nothing = case eq of λ ()
... | just f with Cancel.step action f (GP.cm s)
...   | nothing = case eq of λ ()
...   | just (f′ , c′) = case just-injective eq of λ { refl → same refl }
governor-change (GP.bodyUnwound j) s eq with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
... | just f | just jf with Cancel.pc f
...   | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
...     | just p′ = case just-injective eq of λ { refl → same (restore-frames (Sub.execution jf) (GP.machine s)) }
...     | nothing = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | just f | just jf | Cancel.finished Cancel.cleanupComplete with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
... | just p′ = case just-injective eq of λ { refl → same (restore-frames (Sub.execution jf) (GP.machine s)) }
... | nothing = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | just f | just jf | Cancel.cleaning active = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | nothing | _ = case eq of λ ()
governor-change (GP.bodyUnwound j) s eq | just f | nothing = case eq of λ ()
governor-change (GP.recoverCloseFailure j) s eq with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with Pool.step (Pool.resumeAfterUnwindError j) (GP.pool s) in advanced
...     | just p′ = case just-injective eq of λ { refl → same refl }
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
governor-change (GP.deregisterCancelled j) s eq with lookup j (Sub.jobs (GP.machine s)) in found | Pool.step (Pool.deregister j) (GP.pool s) in advanced
... | just jf | just p′ with lookup j (Pool.handles (GP.pool s))
...   | just (Pool.deregisterPending Pool.cancelledExit) = case just-injective eq of λ { refl → flags j jf (record jf { deregistered = true }) found refl refl }
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | nothing = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just Pool.bodyRunning = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.bodyReturned result) = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just Pool.bodyUnwinding = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.deregisterPending Pool.normalExit) = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.deregistered ex) = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.resultAvailable ex) = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | nothing | _ = case eq of λ ()
governor-change (GP.deregisterCancelled j) s eq | just jf | nothing = case eq of λ ()


-- The monitor fork deliberately restores its parent frame after launchMonitor.
put-twice : ∀ (j : JobId) (old next : Sub.JobFrame) xs → put j old (put j next xs) ≡ put j old xs
put-twice j old next [] with j ≟ j
... | yes _ = refl
... | no neq = Data.Empty.⊥-elim (neq refl)
put-twice j old next ((k , row) ∷ xs) with j ≟ k in decision
... | yes _ with j ≟ j
...   | yes _ = refl
...   | no neq = Data.Empty.⊥-elim (neq refl)
put-twice j old next ((k , row) ∷ xs) | no _ rewrite decision = cong ((k , row) ∷_) (put-twice j old next xs)
fork-rows : ∀ j c {d} → Sub.advance (Sub.jobStep j J.launchMonitor) c ≡ just d →
 ∀ old → put j old (Sub.jobs d) ≡ put j old (Sub.jobs c)
fork-rows j c eq old with lookup j (Sub.jobs c)
... | nothing = case eq of λ ()
... | just jf with Sub.queued jf | J.step J.launchMonitor (Sub.execution jf) (Sub.world c)
...   | false | just (next , w) = case just-injective eq of λ { refl → put-twice j old (record jf { execution = next }) (Sub.jobs c) }
...   | true | _ = case eq of λ ()
...   | false | nothing = case eq of λ ()

fork-change : ∀ j w s {s′} → PS.fork j w s ≡ just s′ → Effect other (view s) (view s′)
fork-change j (ident wid) s eq with lookup j (Sub.jobs (PS.machine s)) in found | PS.byParent j (PS.monitors s) | PS.freshWorker (ident wid) s
... | just jf | nothing | true with G.kind (J.work (Sub.execution jf)) |
  J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s)) |
  PS.byPeer (J.connectionRef (Sub.execution jf)) (PS.monitors s)
...   | G.establish | J.forkMonitor | true | nothing with
  Sub.advance (Sub.jobStep j J.launchMonitor) (PS.machine s) in spawned |
  BPool.step (BPool.forkConcurrent (ident wid)) (PS.monitorPool s) in forked
...     | just c′ | just p′ = case just-injective eq of λ { refl → flags j jf jf found refl (fork-rows j (PS.machine s) spawned jf) }
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

monitor-delivery-change : ∀ blocked err s {s′} → PS.deliverMonitor blocked err s ≡ just s′ → Effect other (view s) (view s′)
monitor-delivery-change blocked err s eq with BPool.phase (PS.monitorPool s)
... | BPool.cancelPending tid with lookup tid (PS.monitors s)
...   | nothing = case eq of λ ()
...   | just t with PS.monitorDeliverable blocked (PS.pc t) | BPool.step BPool.deliverCancel (PS.monitorPool s) in delivered
...     | true | just p′ with PS.detach err t s in detached
...       | just (f , s′) = case just-injective eq of λ { refl → same (cong Q.View.frames (Q.detach-view err t s detached)) }
...       | nothing = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.cancelPending tid | just t | false | _ = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.cancelPending tid | just t | true | nothing = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.openPool = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.closing = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.closedPool = case eq of λ ()
monitor-delivery-change blocked err s eq | BPool.joinPending tid = case eq of λ ()

supervision-change : ∀ action s {s′} → PS.step action s ≡ just s′ → Effect (supervisionTag action) (view s) (view s′)
supervision-change (PS.run a) s eq with PS.governorAllowed a s
... | false = case eq of λ ()
... | true with GP.step a (PS.governor s) in stepped
...   | nothing = case eq of λ ()
...   | just g′ = case just-injective eq of λ { refl → after-rows (cong Q.View.frames (sym (Q.note-view a s (record s { governor = g′ })))) (governor-change a (PS.governor s) stepped) }
supervision-change (PS.forkMonitor j w) s eq = fork-change j w s eq
supervision-change (PS.registerMonitor tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.parentPC t | BPool.step (BPool.registerConcurrent tid) (PS.monitorPool s) in registered
...   | PS.created | just p′ = case just-injective eq of λ { refl → same refl }
supervision-change (PS.registerMonitor tid) s eq | just t | PS.created | nothing = case eq of λ ()
supervision-change (PS.registerMonitor tid) s eq | just t | PS.registered | _ = case eq of λ ()
supervision-change (PS.registerMonitor tid) s eq | just t | PS.returned | _ = case eq of λ ()
supervision-change (PS.registerMonitor tid) s eq | nothing = case eq of λ ()
supervision-change (PS.returnEstablishment j) s eq with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s)) in found
... | just (tid , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf) in atPC | GP.running j (GP.pool (PS.governor s))
...   | PS.registered | J.forkMonitor | true = case just-injective eq of λ { refl → established j jf (record jf { execution = record (Sub.execution jf) { pc = J.complete (G.establishedOK (PS.peerRef t)) } }) found atPC refl refl }
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
...     | just p′ = case just-injective eq of λ { refl → same refl }
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
...   | true | just (f , s′) = case just-injective eq of λ { refl → same (cong Q.View.frames (Q.detach-view err t s detached)) }
supervision-change (PS.monitorException tid err) s eq | just t | false | _ = case eq of λ ()
supervision-change (PS.monitorException tid err) s eq | just t | true | nothing = case eq of λ ()
supervision-change (PS.monitorException tid err) s eq | nothing = case eq of λ ()
supervision-change (PS.commitMonitorError tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t | lookup (PS.peerRef t) (J.peers (Sub.world (PS.machine s)))
...   | PS.errorWait err | just peer with Peer.demoted (Peer.key peer) (PS.shared s)
...     | true = case just-injective eq of λ { refl → same refl }
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
...   | PS.normalFinishing | just p′ = case just-injective eq of λ { refl → same (cong Q.View.frames (Q.finish-view true (PS.peerRef t) s)) }
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
...     | just p′ = case just-injective eq of λ { refl → same (cong Q.View.frames (Q.finish-view true (PS.peerRef t) s)) }
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
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.churn | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.localRoot | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.ledger | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.governor | nothing with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.readyToFinish | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.deliverCancel) s eq | Scope.finishedScope | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.beginUnwind) s eq with Scope.step (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.requestCancel) s eq with Scope.step (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.join) s eq with Scope.step (PS.governorPoolClosed s) Scope.join (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope Scope.finishClose) s eq with Scope.step (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope (Scope.beginFailure actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope (Scope.bodyExit actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.scope (Scope.publishResult actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.beginMonitorClose order) s eq with Scope.closed (PS.scopes s)
... | false = case eq of λ ()
... | true with BPool.step (BPool.beginClose order) (PS.monitorPool s) in advanced
...   | just p′ = case just-injective eq of λ { refl → same refl }
...   | nothing = case eq of λ ()
supervision-change PS.requestMonitorCancel s eq with BPool.step BPool.requestCancel (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change PS.joinMonitor s eq with BPool.step BPool.join (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change PS.finishMonitorClose s eq with BPool.step BPool.finishClose (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.deregisterMonitor tid) s eq with BPool.step (BPool.deregister tid) (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.publishMonitorResult tid) s eq with BPool.step (BPool.publishAsyncResult tid) (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → same refl }
... | nothing = case eq of λ ()
supervision-change (PS.deliverMonitorCancellation err) s eq = monitor-delivery-change false err s eq
supervision-change (PS.deliverBlockedMonitorCancellation err) s eq = monitor-delivery-change true err s eq
supervision-change (PS.monitorBodyUnwound tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t | PS.interrupted t
...   | PS.cancelling | just f with Cancel.pc f
...     | Cancel.finished Cancel.abandoned with BPool.step (BPool.bodyUnwound tid) (PS.monitorPool s) in advanced
...       | just p′ = case just-injective eq of λ { refl → same (cong Q.View.frames (Q.finish-view false (PS.peerRef t) s)) }
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
