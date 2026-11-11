{-# OPTIONS --guardedness #-}

-- All raw subsystem actions that retain jobs and followups are observed through
-- their actual source writers. Caller-table effects are proved, not assumed.
module ConnectionManagement.Properties.OwnedFramesQuietSource where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (PeerConnectionId; JobId; WorkerId)
open import ConnectionManagement.IGTypes using (clean; errored)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Subsystem as Sub
open Sub using
  (Action; Configuration; advance; world; jobs; monitors; pc; now; publicState; privateState;
   targetInput; completions; maxRetries; clearFailDelay; noMonitor; noCompletions; noTargets; wakeupAt; wakeupReady;
   completeDelays; selectionPC; publishPublic; sampleInputs; prepareWait; selecting;
   cancelTimer; apply; publishView; traceDecision; launch; register; completionAssertionFailed;
   policy; completion; monitor; targets; wakeup; core; publishPublicState; sampleTime; applyAt;
   setTargets; selectMonitor; selectCompletion; selectTargets; selectWakeup; registerWakeup;
   expireWakeup; cancelWakeup; publishCounters; traceSelection; selectPolicy; forkJob;
   registerJob; finishLaunch; jobStep; enqueueCompletion; deregisterJob; protocolResult;
   publishInitiatorResult; pollPeer; monitorStep; monitorFinished; observeInitiatorFailure)
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as Life
open import ConnectionManagement.Properties.OutboundKeys using (KeySame; fields-same; nonkey)

-- Eight changing families have their own ownership lemmas.
quiet : Action → Bool
quiet (core action) = false
quiet (forkJob caller child sock) = false
quiet (jobStep j action) = false
quiet (enqueueCompletion j delay) = false
quiet (deregisterJob j) = false
quiet (pollPeer ref caller) = false
quiet (monitorStep ref action) = false
quiet (monitorFinished ref) = false
quiet _ = true

-- Only world/governor scheduling fields may change in this effect.
Effect : Configuration → Configuration → Set
Effect c d = KeySame (J.cm (world c)) (J.cm (world d)) × jobs d ≡ jobs c × monitors d ≡ monitors c

-- This exhaustive tree follows Subsystem.advance on all quiet constructors.
quiet-effect : ∀ a c {d} → quiet a ≡ true → advance a c ≡ just d → Effect c d

quiet-effect (core action) c () eq
quiet-effect publishPublicState c permit with pc c
... | publishPublic = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect publishPublicState c permit | sampleInputs = λ ()
quiet-effect publishPublicState c permit | prepareWait = λ ()
quiet-effect publishPublicState c permit | selecting = λ ()
quiet-effect publishPublicState c permit | (cancelTimer selected) = λ ()
quiet-effect publishPublicState c permit | (apply selected) = λ ()
quiet-effect publishPublicState c permit | (publishView work) = λ ()
quiet-effect publishPublicState c permit | (traceDecision work) = λ ()
quiet-effect publishPublicState c permit | (launch work) = λ ()
quiet-effect publishPublicState c permit | (register j rest) = λ ()
quiet-effect publishPublicState c permit | (completionAssertionFailed result) = λ ()
quiet-effect (sampleTime t) c permit with pc c | now c ≤? t
... | sampleInputs | yes _ = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
... | sampleInputs | no _ = λ ()
quiet-effect (sampleTime t) c permit | publishPublic | _ = λ ()
quiet-effect (sampleTime t) c permit | prepareWait | _ = λ ()
quiet-effect (sampleTime t) c permit | selecting | _ = λ ()
quiet-effect (sampleTime t) c permit | (cancelTimer selected) | _ = λ ()
quiet-effect (sampleTime t) c permit | (apply selected) | _ = λ ()
quiet-effect (sampleTime t) c permit | (publishView work) | _ = λ ()
quiet-effect (sampleTime t) c permit | (traceDecision work) | _ = λ ()
quiet-effect (sampleTime t) c permit | (launch work) | _ = λ ()
quiet-effect (sampleTime t) c permit | (register j rest) | _ = λ ()
quiet-effect (sampleTime t) c permit | (completionAssertionFailed result) | _ = λ ()
-- Target-input writes leave the stored job frames unchanged.
quiet-effect (setTargets t) c permit = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect (selectMonitor delay) c permit with pc c | G.monitored (J.peers (world c)) (privateState c)
... | selecting | changes@(_ ∷ _) with completeDelays changes delay
...   | false = λ ()
...   | true = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect (selectMonitor delay) c permit | selecting | [] = λ ()
quiet-effect (selectMonitor delay) c permit | publishPublic | _ = λ ()
quiet-effect (selectMonitor delay) c permit | sampleInputs | _ = λ ()
quiet-effect (selectMonitor delay) c permit | prepareWait | _ = λ ()
quiet-effect (selectMonitor delay) c permit | (cancelTimer selected) | _ = λ ()
quiet-effect (selectMonitor delay) c permit | (apply selected) | _ = λ ()
quiet-effect (selectMonitor delay) c permit | (publishView work) | _ = λ ()
quiet-effect (selectMonitor delay) c permit | (traceDecision work) | _ = λ ()
quiet-effect (selectMonitor delay) c permit | (launch work) | _ = λ ()
quiet-effect (selectMonitor delay) c permit | (register j rest) | _ = λ ()
quiet-effect (selectMonitor delay) c permit | (completionAssertionFailed result) | _ = λ ()
quiet-effect selectCompletion c permit with pc c | noMonitor c | completions c in fifo
... | selecting | true | x ∷ xs = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
... | selecting | true | [] = λ ()
... | selecting | false | _ = λ ()
quiet-effect selectCompletion c permit | publishPublic | _ | _ = λ ()
quiet-effect selectCompletion c permit | sampleInputs | _ | _ = λ ()
quiet-effect selectCompletion c permit | prepareWait | _ | _ = λ ()
quiet-effect selectCompletion c permit | (cancelTimer selected) | _ | _ = λ ()
quiet-effect selectCompletion c permit | (apply selected) | _ | _ = λ ()
quiet-effect selectCompletion c permit | (publishView work) | _ | _ = λ ()
quiet-effect selectCompletion c permit | (traceDecision work) | _ | _ = λ ()
quiet-effect selectCompletion c permit | (launch work) | _ | _ = λ ()
quiet-effect selectCompletion c permit | (register j rest) | _ | _ = λ ()
quiet-effect selectCompletion c permit | (completionAssertionFailed result) | _ | _ = λ ()
quiet-effect selectTargets c permit with pc c | noMonitor c | noCompletions c | noTargets c
... | selecting | true | true | false = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect selectTargets c permit | selecting | true | true | true = λ ()
quiet-effect selectTargets c permit | selecting | true | false | true = λ ()
quiet-effect selectTargets c permit | selecting | true | false | false = λ ()
quiet-effect selectTargets c permit | selecting | false | true | true = λ ()
quiet-effect selectTargets c permit | selecting | false | true | false = λ ()
quiet-effect selectTargets c permit | selecting | false | false | true = λ ()
quiet-effect selectTargets c permit | selecting | false | false | false = λ ()
quiet-effect selectTargets c permit | publishPublic | _ | _ | _ = λ ()
quiet-effect selectTargets c permit | sampleInputs | _ | _ | _ = λ ()
quiet-effect selectTargets c permit | prepareWait | _ | _ | _ = λ ()
quiet-effect selectTargets c permit | (cancelTimer selected) | _ | _ | _ = λ ()
quiet-effect selectTargets c permit | (apply selected) | _ | _ | _ = λ ()
quiet-effect selectTargets c permit | (publishView work) | _ | _ | _ = λ ()
quiet-effect selectTargets c permit | (traceDecision work) | _ | _ | _ = λ ()
quiet-effect selectTargets c permit | (launch work) | _ | _ | _ = λ ()
quiet-effect selectTargets c permit | (register j rest) | _ | _ | _ = λ ()
quiet-effect selectTargets c permit | (completionAssertionFailed result) | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit with pc c | noMonitor c | noCompletions c | noTargets c
... | selecting | true | true | true with G.choose (now c) picked (privateState c)
...   | nothing = λ ()
...   | just d = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect (selectPolicy picked) c permit | selecting | true | true | false = λ ()
quiet-effect (selectPolicy picked) c permit | selecting | true | false | true = λ ()
quiet-effect (selectPolicy picked) c permit | selecting | true | false | false = λ ()
quiet-effect (selectPolicy picked) c permit | selecting | false | true | true = λ ()
quiet-effect (selectPolicy picked) c permit | selecting | false | true | false = λ ()
quiet-effect (selectPolicy picked) c permit | selecting | false | false | true = λ ()
quiet-effect (selectPolicy picked) c permit | selecting | false | false | false = λ ()
quiet-effect (selectPolicy picked) c permit | publishPublic | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit | sampleInputs | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit | prepareWait | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit | (cancelTimer selected) | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit | (apply selected) | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit | (publishView work) | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit | (traceDecision work) | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit | (launch work) | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit | (register j rest) | _ | _ | _ = λ ()
quiet-effect (selectPolicy picked) c permit | (completionAssertionFailed result) | _ | _ | _ = λ ()
quiet-effect registerWakeup c permit with pc c
... | prepareWait = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect registerWakeup c permit | publishPublic = λ ()
quiet-effect registerWakeup c permit | sampleInputs = λ ()
quiet-effect registerWakeup c permit | selecting = λ ()
quiet-effect registerWakeup c permit | (cancelTimer selected) = λ ()
quiet-effect registerWakeup c permit | (apply selected) = λ ()
quiet-effect registerWakeup c permit | (publishView work) = λ ()
quiet-effect registerWakeup c permit | (traceDecision work) = λ ()
quiet-effect registerWakeup c permit | (launch work) = λ ()
quiet-effect registerWakeup c permit | (register j rest) = λ ()
quiet-effect registerWakeup c permit | (completionAssertionFailed result) = λ ()
quiet-effect expireWakeup c permit with pc c | wakeupAt c | wakeupReady c
... | selecting | just _ | false = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
... | selecting | just _ | true = λ ()
... | selecting | nothing | _ = λ ()
quiet-effect expireWakeup c permit | publishPublic | _ | _ = λ ()
quiet-effect expireWakeup c permit | sampleInputs | _ | _ = λ ()
quiet-effect expireWakeup c permit | prepareWait | _ | _ = λ ()
quiet-effect expireWakeup c permit | (cancelTimer selected) | _ | _ = λ ()
quiet-effect expireWakeup c permit | (apply selected) | _ | _ = λ ()
quiet-effect expireWakeup c permit | (publishView work) | _ | _ = λ ()
quiet-effect expireWakeup c permit | (traceDecision work) | _ | _ = λ ()
quiet-effect expireWakeup c permit | (launch work) | _ | _ = λ ()
quiet-effect expireWakeup c permit | (register j rest) | _ | _ = λ ()
quiet-effect expireWakeup c permit | (completionAssertionFailed result) | _ | _ = λ ()
quiet-effect cancelWakeup c permit with pc c
... | cancelTimer selected = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect cancelWakeup c permit | publishPublic = λ ()
quiet-effect cancelWakeup c permit | sampleInputs = λ ()
quiet-effect cancelWakeup c permit | prepareWait = λ ()
quiet-effect cancelWakeup c permit | selecting = λ ()
quiet-effect cancelWakeup c permit | (apply selected) = λ ()
quiet-effect cancelWakeup c permit | (publishView work) = λ ()
quiet-effect cancelWakeup c permit | (traceDecision work) = λ ()
quiet-effect cancelWakeup c permit | (launch work) = λ ()
quiet-effect cancelWakeup c permit | (register j rest) = λ ()
quiet-effect cancelWakeup c permit | (completionAssertionFailed result) = λ ()
quiet-effect selectWakeup c permit with pc c | noMonitor c | noCompletions c | noTargets c | wakeupReady c | wakeupAt c | G.firstReady (now c) (privateState c)
... | selecting | true | true | true | true | just deadline | nothing = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
... | selecting | false | _ | _ | _ | _ | _ = λ ()
... | selecting | true | false | _ | _ | _ | _ = λ ()
... | selecting | true | true | false | _ | _ | _ = λ ()
... | selecting | true | true | true | false | _ | _ = λ ()
... | selecting | true | true | true | true | nothing | _ = λ ()
... | selecting | true | true | true | true | just deadline | just ready = λ ()
quiet-effect selectWakeup c permit | publishPublic | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect selectWakeup c permit | sampleInputs | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect selectWakeup c permit | prepareWait | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect selectWakeup c permit | (cancelTimer selected) | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect selectWakeup c permit | (apply selected) | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect selectWakeup c permit | (publishView work) | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect selectWakeup c permit | (traceDecision work) | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect selectWakeup c permit | (launch work) | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect selectWakeup c permit | (register j rest) | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect selectWakeup c permit | (completionAssertionFailed result) | _ | _ | _ | _ | _ | _ = λ ()
quiet-effect (applyAt t) c permit with pc c | now c ≤? t
... | apply (policy d) | yes _ = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
... | apply (completion result) | yes _ with G.completionAssertion result (privateState c)
...   | false = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
...   | true = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect (applyAt t) c permit | apply (monitor changes delay) | yes _ = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect (applyAt t) c permit | apply (targets t′) | yes _ = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect (applyAt t) c permit | apply (wakeup deadline) | yes _ with deadline ≤? t
...   | yes _ = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
...   | no _ = λ ()
quiet-effect (applyAt t) c permit | apply (policy d) | no _ = λ ()
quiet-effect (applyAt t) c permit | apply (completion result) | no _ = λ ()
quiet-effect (applyAt t) c permit | apply (monitor changes delay) | no _ = λ ()
quiet-effect (applyAt t) c permit | apply (targets t′) | no _ = λ ()
quiet-effect (applyAt t) c permit | apply (wakeup deadline) | no _ = λ ()
quiet-effect (applyAt t) c permit | publishPublic | _ = λ ()
quiet-effect (applyAt t) c permit | sampleInputs | _ = λ ()
quiet-effect (applyAt t) c permit | prepareWait | _ = λ ()
quiet-effect (applyAt t) c permit | selecting | _ = λ ()
quiet-effect (applyAt t) c permit | (cancelTimer selected) | _ = λ ()
quiet-effect (applyAt t) c permit | (publishView work) | _ = λ ()
quiet-effect (applyAt t) c permit | (traceDecision work) | _ = λ ()
quiet-effect (applyAt t) c permit | (launch work) | _ = λ ()
quiet-effect (applyAt t) c permit | (register j rest) | _ = λ ()
quiet-effect (applyAt t) c permit | (completionAssertionFailed result) | _ = λ ()
quiet-effect publishCounters c permit with pc c
... | publishView work = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect publishCounters c permit | publishPublic = λ ()
quiet-effect publishCounters c permit | sampleInputs = λ ()
quiet-effect publishCounters c permit | prepareWait = λ ()
quiet-effect publishCounters c permit | selecting = λ ()
quiet-effect publishCounters c permit | (cancelTimer selected) = λ ()
quiet-effect publishCounters c permit | (apply selected) = λ ()
quiet-effect publishCounters c permit | (traceDecision work) = λ ()
quiet-effect publishCounters c permit | (launch work) = λ ()
quiet-effect publishCounters c permit | (register j rest) = λ ()
quiet-effect publishCounters c permit | (completionAssertionFailed result) = λ ()
quiet-effect traceSelection c permit with pc c
... | traceDecision work = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect traceSelection c permit | publishPublic = λ ()
quiet-effect traceSelection c permit | sampleInputs = λ ()
quiet-effect traceSelection c permit | prepareWait = λ ()
quiet-effect traceSelection c permit | selecting = λ ()
quiet-effect traceSelection c permit | (cancelTimer selected) = λ ()
quiet-effect traceSelection c permit | (apply selected) = λ ()
quiet-effect traceSelection c permit | (publishView work) = λ ()
quiet-effect traceSelection c permit | (launch work) = λ ()
quiet-effect traceSelection c permit | (register j rest) = λ ()
quiet-effect traceSelection c permit | (completionAssertionFailed result) = λ ()
quiet-effect registerJob c permit with pc c
... | register j rest = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect registerJob c permit | publishPublic = λ ()
quiet-effect registerJob c permit | sampleInputs = λ ()
quiet-effect registerJob c permit | prepareWait = λ ()
quiet-effect registerJob c permit | selecting = λ ()
quiet-effect registerJob c permit | (cancelTimer selected) = λ ()
quiet-effect registerJob c permit | (apply selected) = λ ()
quiet-effect registerJob c permit | (publishView work) = λ ()
quiet-effect registerJob c permit | (traceDecision work) = λ ()
quiet-effect registerJob c permit | (launch work) = λ ()
quiet-effect registerJob c permit | (completionAssertionFailed result) = λ ()
quiet-effect (forkJob caller child sock) c () eq
quiet-effect finishLaunch c permit with pc c
... | launch [] = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
... | launch (work ∷ rest) = λ ()
quiet-effect finishLaunch c permit | publishPublic = λ ()
quiet-effect finishLaunch c permit | sampleInputs = λ ()
quiet-effect finishLaunch c permit | prepareWait = λ ()
quiet-effect finishLaunch c permit | selecting = λ ()
quiet-effect finishLaunch c permit | (cancelTimer selected) = λ ()
quiet-effect finishLaunch c permit | (apply selected) = λ ()
quiet-effect finishLaunch c permit | (publishView work) = λ ()
quiet-effect finishLaunch c permit | (traceDecision work) = λ ()
quiet-effect finishLaunch c permit | (register j rest) = λ ()
quiet-effect finishLaunch c permit | (completionAssertionFailed result) = λ ()
quiet-effect (jobStep j action) c () eq
quiet-effect (enqueueCompletion j delay) c () eq
quiet-effect (deregisterJob j) c () eq
quiet-effect (protocolResult ref n result) c permit with lookup ref (J.peers (world c))
... | nothing = λ ()
... | just peer with P.step (P.protocolResult n result) peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
...   | nothing = λ ()
...   | just (peer′ , ig′) = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect (publishInitiatorResult ref i) c permit with lookup ref (J.peers (world c))
... | nothing = λ ()
... | just peer with P.takePending i (P.pendingResults peer) | lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c)))))) in observed
...   | just ((n , result) , retained) | just observedMux with Life.muxAllowed (P.muxRef peer) Life.jobAccess (Inbound.handlerLifecycles (CM.core (J.cm (world c))))
...     | false = λ ()
...     | true = λ { refl → fields-same _ _ refl refl refl refl , refl , refl }
quiet-effect (publishInitiatorResult ref i) c permit | just peer | nothing | _ = λ ()
quiet-effect (publishInitiatorResult ref i) c permit | just peer | just selected | nothing = λ ()
quiet-effect (observeInitiatorFailure ref) c permit with lookup ref (J.peers (world c))
... | nothing = λ ()
... | just peer with lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
...   | nothing = λ ()
...   | just observedMux with M.completions observedMux
...     | M.jobResult M.initiatorJob n (errored err) ∷ rest with CM.advance
  (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c)) in stepped
...       | nothing = λ ()
...       | just cm′ = λ { refl → nonkey (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c)) refl stepped , refl , refl }
quiet-effect (observeInitiatorFailure ref) c permit | just peer | just observedMux | [] = λ ()
quiet-effect (observeInitiatorFailure ref) c permit | just peer | just observedMux | M.jobResult M.responderJob n outcome ∷ rest = λ ()
quiet-effect (observeInitiatorFailure ref) c permit | just peer | just observedMux | M.jobResult M.initiatorJob n clean ∷ rest = λ ()
quiet-effect (pollPeer ref caller) c () eq
quiet-effect (monitorStep ref action) c () eq
quiet-effect (monitorFinished ref) c () eq
