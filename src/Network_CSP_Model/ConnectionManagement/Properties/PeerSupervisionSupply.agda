{-# OPTIONS --guardedness #-}

-- Supply bounds and acquisition captures through physical monitor/scope steps.
-- Peer status, job PCs and release stores can change: only the stated observer
-- is transported, not an equality of the complete raw subsystem configuration.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool; true; false)
module ConnectionManagement.Properties.PeerSupervisionSupply (isIOManagerError : ErrorId → Bool) where

open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong₂)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.PeerSupervision as Supervision
module PS = Supervision isIOManagerError
module GP = PS.GP
module Pool = PS.Pool
import ConnectionManagement.Properties.GovernorPoolSupply as GovernorSupply
module Supply = GovernorSupply isIOManagerError
import ConnectionManagement.Properties.OutboundRuntimeSupply as Runtime

Valid : PS.State → Set
Valid s = Supply.Valid (PS.governor s)
Bounded : PS.State → Set
Bounded s = SupplyBounds (PS.shared s)

-- This is exactly the data observed by the existing closed supply invariant.
View : Set
View = A.Runtime × S.State × Store JobId Cancel.Frame
observe : PS.State → View
observe s = CM.acquiring (PS.cm s) , PS.shared s , GP.unwinding (PS.governor s)
Predicate : View → Set
Predicate (runtime , peerWorld , detached) = Runtime.RuntimeValid runtime peerWorld × Supply.Detached detached peerWorld
transport : ∀ before after → observe after ≡ observe before → Valid before → Valid after
transport before after eq = subst Predicate (sym eq)

-- A peer-only write preserves the whole CM observation and detached captures.
finish-observe : ∀ clear ref s → observe (PS.finishPeer clear ref s) ≡ observe s
finish-observe clear ref s with lookup ref (J.peers (Sub.world (PS.machine s)))
... | nothing = refl
... | just peer = refl
note-poll-observe : ∀ ref before after → observe (PS.notePoll ref before after) ≡ observe after
note-poll-observe ref before after with PS.byPeer ref (PS.monitors before) |
  lookup ref (J.peers (Sub.world (PS.machine before))) | lookup ref (J.peers (Sub.world (PS.machine after)))
... | nothing | old | next = refl
... | just pair | nothing | next = refl
... | just pair | just old | nothing = refl
... | just (tid , t) | just old | just next with Peer.monitorStarted next
...   | false = refl
...   | true = refl

-- Background cancellation cannot detach an active acquisition. Its remaining
-- CM change is release bookkeeping, outside the invariant's precise observer.
start-observe : ∀ callerId err c {frame c′} → lookup callerId (CM.acquiring c) ≡ nothing →
  Cancel.start callerId err Cancel.ordinary c ≡ just (frame , c′) →
  CM.acquiring c′ ≡ CM.acquiring c × I.world (CM.core c′) ≡ I.world (CM.core c)
start-observe callerId err c missing eq with lookup callerId (CM.acquiring c)
... | just active = case missing of λ ()
... | nothing with lookup callerId (CM.releasing c)
...   | nothing = case just-injective eq of λ { refl → refl , refl }
...   | just active = case just-injective eq of λ { refl → refl , refl }

detach-observe : ∀ err t s {frame s′} → PS.detach err t s ≡ just (frame , s′) → observe s′ ≡ observe s
detach-observe err t s eq with lookup (PS.worker t) (CM.acquiring (PS.cm s)) in absent
... | just active = case eq of λ ()
... | nothing with lookup (PS.peerRef t) (Sub.monitors (PS.machine s))
...   | nothing with Cancel.start (PS.worker t) err Cancel.ordinary (PS.cm s) in started
...     | nothing = case eq of λ ()
...     | just (frame , c′) = case just-injective eq of λ { refl →
  cong₂ _,_ (proj₁ (start-observe (PS.worker t) err (PS.cm s) absent started))
    (cong₂ _,_ (proj₂ (start-observe (PS.worker t) err (PS.cm s) absent started)) refl) }
detach-observe err t s eq | nothing | just follow with J.caller follow ≟ PS.worker t
... | no neq = case eq of λ ()
... | yes same with Cancel.start (PS.worker t) err Cancel.ordinary (PS.cm s) in started
...   | nothing = case eq of λ ()
...   | just (frame , c′) = case just-injective eq of λ { refl →
  cong₂ _,_ (proj₁ (start-observe (PS.worker t) err (PS.cm s) absent started))
    (cong₂ _,_ (proj₂ (start-observe (PS.worker t) err (PS.cm s) absent started)) refl) }

-- Forking a physical monitor changes peer/job data, not CM allocation stores.
peer-fork-cm : ∀ f peerWorld {peerWorld′} → J.peerStep Peer.forkMonitor f peerWorld ≡ just peerWorld′ → J.cm peerWorld′ ≡ J.cm peerWorld
peer-fork-cm f peerWorld eq with lookup (J.connectionRef f) (J.peers peerWorld)
... | nothing = case eq of λ ()
... | just peer with Peer.monitorStarted peer
...   | true = case eq of λ ()
...   | false = case just-injective eq of λ { refl → refl }
job-launch-cm : ∀ f peerWorld {f′ peerWorld′} → J.step J.launchMonitor f peerWorld ≡ just (f′ , peerWorld′) → J.cm peerWorld′ ≡ J.cm peerWorld
job-launch-cm f peerWorld eq with J.pc f
... | J.forkMonitor with J.peerStep Peer.forkMonitor f peerWorld in advanced
...   | nothing = case eq of λ ()
...   | just peerWorld′ = case just-injective eq of λ { refl → peer-fork-cm f peerWorld advanced }
job-launch-cm f peerWorld eq | J.begin = case eq of λ ()
job-launch-cm f peerWorld eq | J.awaitAcquire = case eq of λ ()
job-launch-cm f peerWorld eq | (J.startBundle temp ns) = case eq of λ ()
job-launch-cm f peerWorld eq | (J.publishBundle temp) = case eq of λ ()
job-launch-cm f peerWorld eq | J.markWarm = case eq of λ ()
job-launch-cm f peerWorld eq | J.finishActivation = case eq of λ ()
job-launch-cm f peerWorld eq | J.awaitHot = case eq of λ ()
job-launch-cm f peerWorld eq | J.awaitAll = case eq of λ ()
job-launch-cm f peerWorld eq | J.callRelease = case eq of λ ()
job-launch-cm f peerWorld eq | J.awaitRelease = case eq of λ ()
job-launch-cm f peerWorld eq | J.delayFailure = case eq of λ ()
job-launch-cm f peerWorld eq | (J.awaitCold result) = case eq of λ ()
job-launch-cm f peerWorld eq | (J.complete result) = case eq of λ ()
job-launch-cm f peerWorld eq | (J.acquirePolicy fault) = case eq of λ ()
job-launch-cm f peerWorld eq | (J.nodeDelivery fault) = case eq of λ ()
job-launch-cm f peerWorld eq | (J.nodeRethrow fault) = case eq of λ ()
sub-launch-cm : ∀ j c {c′} → Sub.advance (Sub.jobStep j J.launchMonitor) c ≡ just c′ →
  J.cm (Sub.world c′) ≡ J.cm (Sub.world c)
sub-launch-cm j c eq with lookup j (Sub.jobs c)
... | nothing = case eq of λ ()
... | just jf with Sub.queued jf | J.step J.launchMonitor (Sub.execution jf) (Sub.world c) in advanced
...   | false | just (f′ , peerWorld′) = case just-injective eq of λ { refl → job-launch-cm (Sub.execution jf) (Sub.world c) advanced }
sub-launch-cm j c eq | just jf | true | any = case eq of λ ()
sub-launch-cm j c eq | just jf | false | nothing = case eq of λ ()

note-governor-observe : ∀ action before after → observe (PS.noteGovernor action before after) ≡ observe after
note-governor-observe (GP.run (Sub.core a)) before after = refl
note-governor-observe (GP.run Sub.publishPublicState) before after = refl
note-governor-observe (GP.run (Sub.sampleTime t)) before after = refl
note-governor-observe (GP.run (Sub.applyAt t)) before after = refl
note-governor-observe (GP.run (Sub.setTargets ts)) before after = refl
note-governor-observe (GP.run (Sub.selectMonitor ds)) before after = refl
note-governor-observe (GP.run Sub.selectCompletion) before after = refl
note-governor-observe (GP.run Sub.selectTargets) before after = refl
note-governor-observe (GP.run Sub.selectWakeup) before after = refl
note-governor-observe (GP.run Sub.registerWakeup) before after = refl
note-governor-observe (GP.run Sub.expireWakeup) before after = refl
note-governor-observe (GP.run Sub.cancelWakeup) before after = refl
note-governor-observe (GP.run Sub.publishCounters) before after = refl
note-governor-observe (GP.run Sub.traceSelection) before after = refl
note-governor-observe (GP.run (Sub.selectPolicy ps)) before after = refl
note-governor-observe (GP.run (Sub.forkJob w child sock)) before after = refl
note-governor-observe (GP.run Sub.registerJob) before after = refl
note-governor-observe (GP.run Sub.finishLaunch) before after = refl
note-governor-observe (GP.run (Sub.jobStep j a)) before after = refl
note-governor-observe (GP.run (Sub.enqueueCompletion j delay)) before after = refl
note-governor-observe (GP.run (Sub.deregisterJob j)) before after = refl
note-governor-observe (GP.run (Sub.protocolResult ref n result)) before after = refl
note-governor-observe (GP.run (Sub.publishInitiatorResult ref i)) before after = refl
note-governor-observe (GP.run (Sub.pollPeer ref w)) before after = note-poll-observe ref before after
note-governor-observe (GP.run (Sub.monitorStep ref a)) before after = refl
note-governor-observe (GP.run (Sub.monitorFinished ref)) before after = refl
note-governor-observe (GP.run (Sub.observeInitiatorFailure ref)) before after = refl
note-governor-observe (GP.handoff w) before after = refl
note-governor-observe (GP.beginClose order) before after = refl
note-governor-observe GP.requestCancel before after = refl
note-governor-observe GP.join before after = refl
note-governor-observe GP.finishClose before after = refl
note-governor-observe (GP.deliverCancellation err) before after = refl
note-governor-observe (GP.deliverOpenCancellation err) before after = refl
note-governor-observe (GP.cleanup j a) before after = refl
note-governor-observe (GP.bodyUnwound j) before after = refl
note-governor-observe (GP.recoverCloseFailure j) before after = refl
note-governor-observe (GP.deregisterCancelled j) before after = refl
note-governor-observe (GP.publishAsyncResult j) before after = refl

-- The fork writer is observed through its actual successful raw peer action.
fork-preserves : ∀ j w s {s′} → PS.fork j w s ≡ just s′ → Valid s → Valid s′
fork-preserves j w s eq valid with lookup j (Sub.jobs (PS.machine s)) | PS.byParent j (PS.monitors s) | PS.freshWorker w s
... | just jf | nothing | true with G.kind (J.work (Sub.execution jf)) |
  J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s)) |
  PS.byPeer (J.connectionRef (Sub.execution jf)) (PS.monitors s)
...   | G.establish | J.forkMonitor | true | nothing with
  Sub.advance (Sub.jobStep j J.launchMonitor) (PS.machine s) in advanced |
  Pool.step (Pool.forkConcurrent (ident (serial w))) (PS.monitorPool s)
...     | just c′ | just p′ = case just-injective eq of λ { refl →
  subst (λ c → Runtime.Valid c × Supply.Detached (GP.unwinding (PS.governor s)) (I.world (CM.core c)))
    (sym (sub-launch-cm j (PS.machine s) advanced)) valid }
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | nothing | any = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | just c′ | nothing = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.forget | pc | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.activate | pc | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.close | pc | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.deactivate | pc | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.begin | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.awaitAcquire | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.startBundle temp ns) | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.publishBundle temp) | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.markWarm | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.finishActivation | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.awaitHot | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.awaitAll | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.callRelease | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.awaitRelease | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.delayFailure | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.awaitCold result) | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.complete result) | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.acquirePolicy fault) | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.nodeDelivery fault) | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.nodeRethrow fault) | running | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.forkMonitor | false | peer = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.forkMonitor | true | just peer = case eq of λ ()
fork-preserves j w s eq valid | nothing | any | fresh = case eq of λ ()
fork-preserves j w s eq valid | just jf | just previous | fresh = case eq of λ ()
fork-preserves j w s eq valid | just jf | nothing | false = case eq of λ ()

-- Cancellation delivery can change release bookkeeping but preserves each
-- active acquisition capture, the shared heap, and governor cleanup captures.
delivery-preserves : ∀ blocked err s {s′} → PS.deliverMonitor blocked err s ≡ just s′ → Valid s → Valid s′
delivery-preserves blocked err s eq valid with Pool.phase (PS.monitorPool s)
... | Pool.cancelPending tid with lookup tid (PS.monitors s)
...   | nothing = case eq of λ ()
...   | just t with PS.monitorDeliverable blocked (PS.pc t) | Pool.step Pool.deliverCancel (PS.monitorPool s)
...     | true | just p′ with PS.detach err t s in detached
...       | nothing = case eq of λ ()
...       | just (f , s′) = case just-injective eq of λ { refl → transport s s′ (detach-observe err t s detached) valid }
delivery-preserves blocked err s eq valid | Pool.cancelPending tid | just t | false | any = case eq of λ ()
delivery-preserves blocked err s eq valid | Pool.cancelPending tid | just t | true | nothing = case eq of λ ()
delivery-preserves blocked err s eq valid | Pool.openPool = case eq of λ ()
delivery-preserves blocked err s eq valid | Pool.closing = case eq of λ ()
delivery-preserves blocked err s eq valid | Pool.closedPool = case eq of λ ()
delivery-preserves blocked err s eq valid | (Pool.joinPending j) = case eq of λ ()

step-preserves : ∀ action s {s′} → PS.step action s ≡ just s′ → Valid s → Valid s′
step-preserves (PS.run action) s eq valid with PS.governorAllowed action s
... | false = case eq of λ ()
... | true with GP.step action (PS.governor s) in advanced
...   | nothing = case eq of λ ()
...   | just g′ = case just-injective eq of λ { refl →
  transport (record s { governor = g′ }) (PS.noteGovernor action s (record s { governor = g′ }))
    (note-governor-observe action s (record s { governor = g′ }))
    (Supply.step-preserves action (PS.governor s) advanced valid) }
step-preserves (PS.forkMonitor j w) s eq valid = fork-preserves j w s eq valid
step-preserves (PS.registerMonitor tid) s eq valid with lookup tid (PS.monitors s)
... | nothing = case eq of λ ()
... | just t with PS.parentPC t | Pool.step (Pool.registerConcurrent tid) (PS.monitorPool s)
...   | PS.created | just p′ = case just-injective eq of λ { refl → valid }
step-preserves (PS.registerMonitor tid) s eq valid | just t | PS.registered | any = case eq of λ ()
step-preserves (PS.registerMonitor tid) s eq valid | just t | PS.returned | any = case eq of λ ()
step-preserves (PS.registerMonitor tid) s eq valid | just t | PS.created | nothing = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
... | just (tid , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s))
...   | PS.registered | J.forkMonitor | true = case just-injective eq of λ { refl → valid }
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.begin | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.awaitAcquire | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | (J.startBundle temp ns) | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | (J.publishBundle temp) | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.markWarm | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.finishActivation | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.awaitHot | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.awaitAll | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.callRelease | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.awaitRelease | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.delayFailure | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | (J.awaitCold result) | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | (J.complete result) | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | (J.acquirePolicy fault) | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | (J.nodeDelivery fault) | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | (J.nodeRethrow fault) | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.created | pc | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.returned | pc | running = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just (tid , t) | just jf | PS.registered | J.forkMonitor | false = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | nothing | any = case eq of λ ()
step-preserves (PS.returnEstablishment j) s eq valid | just pair | nothing = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
... | just pair | just jf with PS.parentPC (proj₂ pair) | J.pc (Sub.execution jf)
...   | PS.returned | J.complete result with GP.Pool.step
  (GP.Pool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (PS.governor s))
...     | nothing = case eq of λ ()
...     | just p′ = case just-injective eq of λ { refl → valid }
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.begin = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.awaitAcquire = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | (J.startBundle temp ns) = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | (J.publishBundle temp) = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.markWarm = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.finishActivation = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.awaitHot = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.awaitAll = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.callRelease = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.awaitRelease = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.delayFailure = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | (J.awaitCold result) = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | (J.acquirePolicy fault) = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | (J.nodeDelivery fault) = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | (J.nodeRethrow fault) = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.returned | J.forkMonitor = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.created | pc = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | just jf | PS.registered | pc = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | nothing | any = case eq of λ ()
step-preserves (PS.finishEstablishment j) s eq valid | just pair | nothing = case eq of λ ()
step-preserves (PS.monitorException tid err) s eq valid with lookup tid (PS.monitors s)
... | nothing = case eq of λ ()
... | just t with PS.bodyActive tid t s | PS.detach err t s in detached
...   | true | just (f , s′) = case just-injective eq of λ { refl → transport s s′ (detach-observe err t s detached) valid }
step-preserves (PS.monitorException tid err) s eq valid | just t | false | any = case eq of λ ()
step-preserves (PS.monitorException tid err) s eq valid | just t | true | nothing = case eq of λ ()
step-preserves (PS.commitMonitorError tid) s eq valid with lookup tid (PS.monitors s)
... | nothing = case eq of λ ()
... | just t with PS.pc t | lookup (PS.peerRef t) (J.peers (Sub.world (PS.machine s)))
...   | PS.errorWait err | just peer with Peer.demoted (Peer.key peer) (PS.shared s)
...     | false = case eq of λ ()
...     | true = case just-injective eq of λ { refl → valid }
step-preserves (PS.commitMonitorError tid) s eq valid | just t | PS.observing | peer = case eq of λ ()
step-preserves (PS.commitMonitorError tid) s eq valid | just t | PS.normalFinishing | peer = case eq of λ ()
step-preserves (PS.commitMonitorError tid) s eq valid | just t | PS.cancelling | peer = case eq of λ ()
step-preserves (PS.commitMonitorError tid) s eq valid | just t | PS.exited | peer = case eq of λ ()
step-preserves (PS.commitMonitorError tid) s eq valid | just t | (PS.errorFinishing err) | peer = case eq of λ ()
step-preserves (PS.commitMonitorError tid) s eq valid | just t | PS.errorWait err | nothing = case eq of λ ()
step-preserves (PS.finishMonitor tid) s eq valid with lookup tid (PS.monitors s)
... | nothing = case eq of λ ()
... | just t with PS.pc t | Pool.step (Pool.bodyReturnedWith tid nothing) (PS.monitorPool s)
...   | PS.normalFinishing | just p′ = case just-injective eq of λ { refl → transport s (PS.finishPeer true (PS.peerRef t) s) (finish-observe true (PS.peerRef t) s) valid }
step-preserves (PS.finishMonitor tid) s eq valid | just t | PS.observing | pool = case eq of λ ()
step-preserves (PS.finishMonitor tid) s eq valid | just t | PS.cancelling | pool = case eq of λ ()
step-preserves (PS.finishMonitor tid) s eq valid | just t | PS.exited | pool = case eq of λ ()
step-preserves (PS.finishMonitor tid) s eq valid | just t | (PS.errorWait err) | pool = case eq of λ ()
step-preserves (PS.finishMonitor tid) s eq valid | just t | (PS.errorFinishing err) | pool = case eq of λ ()
step-preserves (PS.finishMonitor tid) s eq valid | just t | PS.normalFinishing | nothing = case eq of λ ()
step-preserves (PS.finishMonitorError tid) s eq valid with lookup tid (PS.monitors s)
... | nothing = case eq of λ ()
... | just t with PS.pc t
...   | PS.errorFinishing err with Pool.step (Pool.bodyReturnedWith tid (just err)) (PS.monitorPool s)
...     | nothing = case eq of λ ()
...     | just p′ = case just-injective eq of λ { refl → transport s (PS.finishPeer true (PS.peerRef t) s) (finish-observe true (PS.peerRef t) s) valid }
step-preserves (PS.finishMonitorError tid) s eq valid | just t | PS.observing = case eq of λ ()
step-preserves (PS.finishMonitorError tid) s eq valid | just t | PS.normalFinishing = case eq of λ ()
step-preserves (PS.finishMonitorError tid) s eq valid | just t | PS.cancelling = case eq of λ ()
step-preserves (PS.finishMonitorError tid) s eq valid | just t | PS.exited = case eq of λ ()
step-preserves (PS.finishMonitorError tid) s eq valid | just t | (PS.errorWait err) = case eq of λ ()
step-preserves (PS.scope Scope.deliverCancel) s eq valid with Scope.cursor (PS.scopes s) | GP.Pool.parentFork (GP.pool (PS.governor s))
... | Scope.closing Scope.governor | just j = case eq of λ ()
step-preserves (PS.scope Scope.deliverCancel) s eq valid | Scope.closing Scope.governor | nothing with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.deliverCancel) s eq valid | Scope.openScope | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.deliverCancel) s eq valid | Scope.readyToFinish | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.deliverCancel) s eq valid | Scope.finishedScope | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.deliverCancel) s eq valid | Scope.closing Scope.churn | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.deliverCancel) s eq valid | Scope.closing Scope.localRoot | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.deliverCancel) s eq valid | Scope.closing Scope.ledger | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.beginUnwind) s eq valid with Scope.step (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.requestCancel) s eq valid with Scope.step (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.join) s eq valid with Scope.step (PS.governorPoolClosed s) Scope.join (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope Scope.finishClose) s eq valid with Scope.step (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope (Scope.bodyExit actor)) s eq valid with Scope.step (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope (Scope.publishResult actor)) s eq valid with Scope.step (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.scope (Scope.beginFailure actor)) s eq valid with Scope.step (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → valid }
step-preserves (PS.beginMonitorClose order) s eq valid with Scope.closed (PS.scopes s)
... | false = case eq of λ ()
... | true with Pool.step (Pool.beginClose order) (PS.monitorPool s)
...   | nothing = case eq of λ ()
...   | just p′ = case just-injective eq of λ { refl → valid }
step-preserves PS.requestMonitorCancel s eq valid with Pool.step Pool.requestCancel (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves PS.joinMonitor s eq valid with Pool.step Pool.join (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves PS.finishMonitorClose s eq valid with Pool.step Pool.finishClose (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves (PS.deregisterMonitor tid) s eq valid with Pool.step (Pool.deregister tid) (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves (PS.publishMonitorResult tid) s eq valid with Pool.step (Pool.publishAsyncResult tid) (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves (PS.deliverMonitorCancellation err) s eq valid = delivery-preserves false err s eq valid
step-preserves (PS.deliverBlockedMonitorCancellation err) s eq valid = delivery-preserves true err s eq valid
step-preserves (PS.monitorBodyUnwound tid) s eq valid with lookup tid (PS.monitors s)
... | nothing = case eq of λ ()
... | just t with PS.pc t | PS.interrupted t
...   | PS.cancelling | just f with Cancel.pc f
...     | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound tid) (PS.monitorPool s)
...       | nothing = case eq of λ ()
...       | just p′ = case just-injective eq of λ { refl → transport s (PS.finishPeer false (PS.peerRef t) s) (finish-observe false (PS.peerRef t) s) valid }
step-preserves (PS.monitorBodyUnwound tid) s eq valid | just t | PS.cancelling | just f | Cancel.cleaning active = case eq of λ ()
step-preserves (PS.monitorBodyUnwound tid) s eq valid | just t | PS.cancelling | just f | Cancel.finished Cancel.cleanupComplete = case eq of λ ()
step-preserves (PS.monitorBodyUnwound tid) s eq valid | just t | PS.cancelling | just f | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
step-preserves (PS.monitorBodyUnwound tid) s eq valid | just t | PS.observing | interrupted = case eq of λ ()
step-preserves (PS.monitorBodyUnwound tid) s eq valid | just t | PS.normalFinishing | interrupted = case eq of λ ()
step-preserves (PS.monitorBodyUnwound tid) s eq valid | just t | PS.exited | interrupted = case eq of λ ()
step-preserves (PS.monitorBodyUnwound tid) s eq valid | just t | (PS.errorWait err) | interrupted = case eq of λ ()
step-preserves (PS.monitorBodyUnwound tid) s eq valid | just t | (PS.errorFinishing err) | interrupted = case eq of λ ()
step-preserves (PS.monitorBodyUnwound tid) s eq valid | just t | PS.cancelling | nothing = case eq of λ ()

exec-preserves : ∀ {s actions s′} → PS.Executes s actions s′ → Valid s → Valid s′
exec-preserves PS.done valid = valid
exec-preserves (PS.next {s = s} {a = a} eq path) valid = exec-preserves path (step-preserves a s eq valid)
initial-valid : ∀ c g → SupplyBounds (I.world c) → Valid (PS.initial (CM.initial c) g)
initial-valid c g bounded = Supply.initial-valid c g bounded
from-initial-valid : ∀ {c g actions s} → SupplyBounds (I.world c) →
  PS.Executes (PS.initial (CM.initial c) g) actions s → Valid s
from-initial-valid {c} {g} bounded path = exec-preserves path (initial-valid c g bounded)
from-initial : ∀ {c g actions s} → SupplyBounds (I.world c) →
  PS.Executes (PS.initial (CM.initial c) g) actions s → Bounded s
from-initial bounded path = proj₂ (proj₁ (from-initial-valid bounded path))
