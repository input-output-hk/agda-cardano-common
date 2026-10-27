{-# OPTIONS --guardedness #-}

-- Physical PSA monitor threads and outer Async scopes over the governor pool.
-- Captured thread identities are distinct from temporary Sub.monitors jobs.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.PeerSupervision (isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (worker)
open import ConnectionManagement.Store using (Store; lookup; put; delete)
import ConnectionManagement.GovernorPool as Governor
module GP = Governor isIOManagerError
import ConnectionManagement.Rules.JobPoolKernel as Kernel
module Pool = Kernel (Maybe ErrorId) false
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.State as S

-- Each spawning job has its own masked registration gap. Returned means the
-- PSA bracket has exited; the governor job may not yet have returned its result.
data ParentPC : Set where
  created registered returned : ParentPC
data MonitorPC : Set where
  observing normalFinishing cancelling exited : MonitorPC
  errorWait errorFinishing : ErrorId → MonitorPC
record Thread : Set where
  constructor thread
  field peerRef : PeerConnectionId
        worker : WorkerId
        parent : JobId
        parentPC : ParentPC
        pc : MonitorPC
        interrupted : Maybe Cancel.Frame
        followup : Maybe J.Frame
open Thread public

record State : Set where
  constructor supervising
  field governor : GP.State
        monitors : Store JobId Thread
        monitorPool : Pool.State
        scopes : Scope.State
open State public

initial : CM.Configuration → G.State → State
initial c g = supervising (GP.initial c g) [] Pool.initial Scope.initial
machine : State → Sub.Configuration
machine s = GP.machine (governor s)
cm : State → CM.Configuration
cm s = GP.cm (governor s)
shared : State → S.State
shared s = Inbound.world (CM.core (cm s))
setMachine : Sub.Configuration → State → State
setMachine c s = record s { governor = record (governor s)
  { source = record (GP.source (governor s)) { machine = c } } }

-- Peer incarnation and physical worker are captured once at actual creation.
byPeer : PeerConnectionId → Store JobId Thread → Maybe (JobId × Thread)
byPeer ref [] = nothing
byPeer ref ((tid , t) ∷ rest) with ref ≟ peerRef t
... | yes _ = just (tid , t)
... | no _ = byPeer ref rest
byParent : JobId → Store JobId Thread → Maybe (JobId × Thread)
byParent j [] = nothing
byParent j ((tid , t) ∷ rest) with j ≟ parent t
... | yes _ = just (tid , t)
... | no _ = byParent j rest
byWorker : WorkerId → Store JobId Thread → Maybe (JobId × Thread)
byWorker w [] = nothing
byWorker w ((tid , t) ∷ rest) with w ≟ worker t
... | yes _ = just (tid , t)
... | no _ = byWorker w rest

-- A symbolic Async identity is fresh even relative to historical actors.
jobWorkerFree : WorkerId → Store JobId Sub.JobFrame → Bool
jobWorkerFree w [] = true
jobWorkerFree w ((_ , jf) ∷ rest) with w ≟ J.caller (Sub.execution jf) | w ≟ J.child (Sub.execution jf)
... | no _ | no _ = jobWorkerFree w rest
... | _ | _ = false
freshWorker : WorkerId → State → Bool
freshWorker w s with byWorker w (monitors s) | lookup w (S.admissions (shared s)) |
  lookup w (S.handlers (shared s)) | lookup w (S.cleanups (shared s)) |
  lookup w (CM.acquiring (cm s)) | lookup w (CM.releasing (cm s))
... | nothing | nothing | nothing | nothing | nothing | nothing = jobWorkerFree w (Sub.jobs (machine s))
... | _ | _ | _ | _ | _ | _ = false

-- Monitor followups run on their captured thread, not a fresh supplied caller.
threadRunning : JobId → Thread → State → Bool
threadRunning tid t s with lookup tid (Pool.handles (monitorPool s)) | pc t
... | just Pool.bodyRunning | observing = true
... | _ | _ = false
parentMasked : JobId → State → Bool
parentMasked j s with byParent j (monitors s)
... | just (_ , t) with parentPC t
...   | created = true
...   | _ = false
parentMasked j s | nothing = false
parentPending : JobId → State → Bool
parentPending j s with byParent j (monitors s)
... | nothing = false
... | just (_ , t) with parentPC t
...   | returned = false
...   | _ = true

governorPoolClosed : State → Bool
governorPoolClosed s with GP.Pool.phase (GP.pool (governor s))
... | GP.Pool.closedPool = true
... | _ = false
governorMayRun : State → Bool
governorMayRun s with Scope.threads (scopes s) Scope.governor
... | Scope.running = true
... | Scope.cancelRequested = true
... | _ = false
isOwner : Sub.Action → Bool
isOwner (Sub.forkJob _ _ _) = true
isOwner Sub.registerJob = true
isOwner a = GP.ownerAction a

-- Followup completion is not physical monitor completion. Failed operations
-- require the explicit synchronous-error handler rather than silent recursion.
followupFinished : PeerConnectionId → State → Bool
followupFinished ref s with lookup ref (Sub.monitors (machine s))
... | just f with J.pc f
...   | J.complete G.succeeded = true
...   | _ = false
followupFinished ref s | nothing = false
monitorActionAllowed : PeerConnectionId → State → Bool
monitorActionAllowed ref s with byPeer ref (monitors s)
... | nothing = false
... | just (tid , t) = threadRunning tid t s
-- Existing followups must still belong to the same physical thread. This also
-- rejects forged snapshots instead of relying only on creation provenance.
followupOwned : PeerConnectionId → Thread → State → Bool
followupOwned ref t s with lookup ref (Sub.monitors (machine s))
... | nothing = true
... | just f = does (J.caller f ≟ worker t)
ownedMonitorAction : PeerConnectionId → State → Bool
ownedMonitorAction ref s with byPeer ref (monitors s)
... | nothing = false
... | just (tid , t) = threadRunning tid t s ∧ followupOwned ref t s
callerAllowed : WorkerId → State → Bool
callerAllowed w s with byWorker w (monitors s)
... | nothing = true
... | just (tid , t) = threadRunning tid t s
rawAllowed : Sub.Action → State → Bool
rawAllowed (Sub.jobStep _ J.launchMonitor) s = false
rawAllowed (Sub.jobStep j _) s with parentPending j s
... | true = false
... | false = true
rawAllowed (Sub.pollPeer ref w) s with byPeer ref (monitors s)
... | nothing = false
... | just (tid , t) = threadRunning tid t s ∧ does (w ≟ worker t) ∧ followupOwned ref t s
rawAllowed (Sub.monitorStep ref _) s = ownedMonitorAction ref s
rawAllowed (Sub.monitorFinished ref) s = ownedMonitorAction ref s ∧ followupFinished ref s
rawAllowed (Sub.core (CM.beginAcquire w _)) s with byWorker w (monitors s)
... | just _ = false
... | nothing = true
rawAllowed (Sub.core (CM.beginRelease w _)) s with byWorker w (monitors s)
... | just _ = false
... | nothing = true
rawAllowed (Sub.core (CM.acquire w _)) s = callerAllowed w s
rawAllowed (Sub.core (CM.release w _)) s = callerAllowed w s
rawAllowed a s with isOwner a
... | true = governorMayRun s
... | false = true

-- Only the cancelled parent's own mask delays its delivery; other parents,
-- monitors and handler/IG actions can still run during any registration gap.
governorAllowed : GP.Action → State → Bool
governorAllowed (GP.run action) s = rawAllowed action s
governorAllowed (GP.beginClose _) s with Scope.threads (scopes s) Scope.governor
... | Scope.cancelDelivered = true
... | Scope.bodyUnwinding = true
... | _ = false
governorAllowed (GP.deliverCancellation _) s with GP.Pool.phase (GP.pool (governor s))
... | GP.Pool.cancelPending j with parentMasked j s
...   | true = false
...   | false = true
governorAllowed (GP.deliverCancellation _) s | _ = true
governorAllowed (GP.deliverOpenCancellation _) s with GP.Pool.phase (GP.pool (governor s))
... | GP.Pool.cancelPending j with parentMasked j s
...   | true = false
...   | false = true
governorAllowed (GP.deliverOpenCancellation _) s | _ = true
governorAllowed _ s = true

-- A demotion observed inside a still-active followup does not return the
-- physical loop yet; first let that operation observe Cold and finish.
afterPoll : Maybe J.Frame → MonitorPC
afterPoll nothing = normalFinishing
afterPoll (just _) = observing

-- Preserve the promotion-time variable until the separate exit trace clears
-- it. Raw poll coalesces these fields, so refine that boundary in this adapter.
notePoll : PeerConnectionId → State → State → State
notePoll ref before after with byPeer ref (monitors before) |
  lookup ref (J.peers (Sub.world (machine before))) | lookup ref (J.peers (Sub.world (machine after)))
... | just (tid , t) | just old | just next with Peer.monitorStarted next
...   | false = record (setMachine (record (machine after) { world = record (Sub.world (machine after))
  { peers = put ref (record next { monitorStarted = true; promotedAt = Peer.promotedAt old })
    (J.peers (Sub.world (machine after))) } }) after)
  { monitors = put tid (record t { pc = afterPoll (lookup ref (Sub.monitors (machine after))) }) (monitors after) }
...   | true = after
notePoll ref before after | _ | _ | _ = after
noteGovernor : GP.Action → State → State → State
noteGovernor (GP.run (Sub.pollPeer ref _)) before after = notePoll ref before after
noteGovernor _ before after = after

data Action : Set where
  run : GP.Action → Action
  forkMonitor : JobId → WorkerId → Action
  registerMonitor : JobId → Action
  returnEstablishment finishEstablishment : JobId → Action
  monitorException : JobId → ErrorId → Action
  commitMonitorError finishMonitorError finishMonitor : JobId → Action
  scope : Scope.Action → Action
  beginMonitorClose : List JobId → Action
  requestMonitorCancel joinMonitor finishMonitorClose : Action
  deliverMonitorCancellation deliverBlockedMonitorCancellation : ErrorId → Action
  monitorBodyUnwound deregisterMonitor publishMonitorResult : JobId → Action

-- Fork through the real shared peer action, deferring registry insertion and
-- successful PSA return. The original J.forkMonitor PC remains the bracket PC.
fork : JobId → WorkerId → State → Maybe State
fork j w s with lookup j (Sub.jobs (machine s)) | byParent j (monitors s) | freshWorker w s
... | just jf | nothing | true with G.kind (J.work (Sub.execution jf)) |
  J.pc (Sub.execution jf) | GP.running j (GP.pool (governor s)) |
  byPeer (J.connectionRef (Sub.execution jf)) (monitors s)
...   | G.establish | J.forkMonitor | true | nothing with
  Sub.advance (Sub.jobStep j J.launchMonitor) (machine s) |
  Pool.step (Pool.forkConcurrent (ident (serial w))) (monitorPool s)
...     | just c′ | just p′ = just (record (setMachine
    (record c′ { jobs = put j jf (Sub.jobs c′) }) s)
  { monitorPool = p′; monitors = put (ident (serial w))
    (thread (J.connectionRef (Sub.execution jf)) w j created observing nothing nothing) (monitors s) })
...     | _ | _ = nothing
fork j w s | just jf | nothing | true | _ | _ | _ | _ = nothing
fork j w s | _ | _ | _ = nothing

-- Interrupted followups are detached, not completed as ordinary failed jobs.
detach : ErrorId → Thread → State → Maybe (Cancel.Frame × State)
detach err t s with lookup (worker t) (CM.acquiring (cm s))
... | just _ = nothing
... | nothing with lookup (peerRef t) (Sub.monitors (machine s))
...   | nothing with Cancel.start (worker t) err Cancel.ordinary (cm s)
...     | just (f , c′) = just (f , record s { governor = GP.setCM c′ (governor s) })
...     | nothing = nothing
detach err t s | nothing | just follow with J.caller follow ≟ worker t
... | no _ = nothing
... | yes _ with Cancel.start (worker t) err Cancel.ordinary (cm s)
...   | nothing = nothing
...   | just (f , c′) = just (f , setMachine
  (record (GP.machine (GP.setCM c′ (governor s)))
    { monitors = delete (peerRef t) (Sub.monitors (machine s)) })
  (record s { governor = GP.setCM c′ (governor s) }))

-- Synchronous exceptions can also arise during the normal exit trace.
canThrow : MonitorPC → Bool
canThrow observing = true
canThrow normalFinishing = true
canThrow _ = false
bodyActive : JobId → Thread → State → Bool
bodyActive tid t s with lookup tid (Pool.handles (monitorPool s))
... | just Pool.bodyRunning = canThrow (pc t)
... | _ = false

-- Clearing only monitorStarted is diagnostic thread-exit bookkeeping. The
-- normal/error duration trace also clears promotedAt; async cancellation does not.
finishPeer : Bool → PeerConnectionId → State → State
finishPeer clear ref s with lookup ref (J.peers (Sub.world (machine s)))
... | nothing = s
... | just p = setMachine (record (machine s) { world = record (Sub.world (machine s))
  { peers = put ref (record p { monitorStarted = false; promotedAt = duration clear (Peer.promotedAt p) })
    (J.peers (Sub.world (machine s))) } }) s
  where
  duration : Bool → Maybe ℕ → Maybe ℕ
  duration true old = nothing
  duration false old = old

-- A synchronous handler's blocking demotion wait is a separate interruptible
-- input. Ordinary delivery cannot pretend that a masked handler is unmasked.
monitorDeliverable : Bool → MonitorPC → Bool
monitorDeliverable _ observing = true
monitorDeliverable _ normalFinishing = true
monitorDeliverable true (errorWait _) = true
monitorDeliverable true (errorFinishing _) = true
monitorDeliverable _ _ = false
deliverMonitor : Bool → ErrorId → State → Maybe State
deliverMonitor blocked err s with Pool.phase (monitorPool s)
... | Pool.cancelPending tid with lookup tid (monitors s)
...   | nothing = nothing
...   | just t with monitorDeliverable blocked (pc t) | Pool.step Pool.deliverCancel (monitorPool s)
...     | true | just p′ with detach err t s
...       | just (f , s′) = just (record s′ { monitorPool = p′; monitors = put tid
  (record t { pc = cancelling; interrupted = just (record f { cancelError = err })
            ; followup = lookup (peerRef t) (Sub.monitors (machine s)) }) (monitors s′) })
...       | nothing = nothing
deliverMonitor blocked err s | Pool.cancelPending tid | just t | _ | _ = nothing
deliverMonitor blocked err s | _ = nothing

step : Action → State → Maybe State
step (run a) s with governorAllowed a s
... | false = nothing
... | true with GP.step a (governor s)
...   | nothing = nothing
...   | just g′ = just (noteGovernor a s (record s { governor = g′ }))
step (forkMonitor j w) s = fork j w s
step (registerMonitor tid) s with lookup tid (monitors s)
... | just t with parentPC t | Pool.step (Pool.registerConcurrent tid) (monitorPool s)
...   | created | just p′ = just (record s { monitorPool = p′; monitors = put tid
  (record t { parentPC = registered }) (monitors s) })
...   | _ | _ = nothing
step (registerMonitor tid) s | nothing = nothing
step (returnEstablishment j) s with byParent j (monitors s) | lookup j (Sub.jobs (machine s))
... | just (tid , t) | just jf with parentPC t | J.pc (Sub.execution jf) | GP.running j (GP.pool (governor s))
...   | registered | J.forkMonitor | true = just (record (setMachine (record (machine s)
  { jobs = put j (record jf { execution = record (Sub.execution jf) { pc = J.complete (G.establishedOK (peerRef t)) } })
    (Sub.jobs (machine s)) }) s) { monitors = put tid (record t { parentPC = returned }) (monitors s) })
...   | _ | _ | _ = nothing
step (returnEstablishment j) s | _ | _ = nothing
step (finishEstablishment j) s with byParent j (monitors s) | lookup j (Sub.jobs (machine s))
... | just (_ , t) | just jf with parentPC t | J.pc (Sub.execution jf)
...   | returned | J.complete result with GP.Pool.step
    (GP.Pool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (governor s))
...     | just p′ = just (record s { governor = record (governor s) { pool = p′ } })
...     | nothing = nothing
step (finishEstablishment j) s | just (_ , t) | just jf | _ | _ = nothing
step (finishEstablishment j) s | _ | _ = nothing
step (monitorException tid err) s with lookup tid (monitors s)
... | just t with bodyActive tid t s | detach err t s
...   | true | just (f , s′) = just (record s′ { monitors = put tid
  (record t { pc = errorWait err; interrupted = just f
            ; followup = lookup (peerRef t) (Sub.monitors (machine s)) }) (monitors s′) })
...   | _ | _ = nothing
step (monitorException tid err) s | nothing = nothing
step (commitMonitorError tid) s with lookup tid (monitors s)
... | just t with pc t | lookup (peerRef t) (J.peers (Sub.world (machine s)))
...   | errorWait err | just peer with Peer.demoted (Peer.key peer) (shared s)
...     | true = just (record (setMachine (record (machine s) { world = record (Sub.world (machine s))
  { peers = put (peerRef t) (record peer { status = Peer.peerCold }) (J.peers (Sub.world (machine s))) } }) s)
  { monitors = put tid (record t { pc = errorFinishing err }) (monitors s) })
...     | false = nothing
step (commitMonitorError tid) s | just t | _ | _ = nothing
step (commitMonitorError tid) s | nothing = nothing
step (finishMonitor tid) s with lookup tid (monitors s)
... | just t with pc t | Pool.step (Pool.bodyReturnedWith tid nothing) (monitorPool s)
...   | normalFinishing | just p′ = just (record (finishPeer true (peerRef t) s)
  { monitorPool = p′; monitors = put tid (record t { pc = exited }) (monitors s) })
...   | _ | _ = nothing
step (finishMonitor tid) s | nothing = nothing
step (finishMonitorError tid) s with lookup tid (monitors s)
... | just t with pc t
...   | errorFinishing err with Pool.step (Pool.bodyReturnedWith tid (just err)) (monitorPool s)
...     | just p′ = just (record (finishPeer true (peerRef t) s)
  { monitorPool = p′; monitors = put tid (record t { pc = exited }) (monitors s) })
...     | nothing = nothing
step (finishMonitorError tid) s | just t | _ = nothing
step (finishMonitorError tid) s | nothing = nothing
-- Masked governor fork/insertion cannot be interrupted by its supervising scope.
step (scope Scope.deliverCancel) s with Scope.cursor (scopes s) | GP.Pool.parentFork (GP.pool (governor s))
... | Scope.closing Scope.governor | just _ = nothing
... | _ | _ with Scope.step (governorPoolClosed s) Scope.deliverCancel (scopes s)
...   | just next = just (record s { scopes = next })
...   | nothing = nothing
step (scope a) s with Scope.step (governorPoolClosed s) a (scopes s)
... | just next = just (record s { scopes = next })
... | nothing = nothing
step (beginMonitorClose order) s with Scope.closed (scopes s)
... | false = nothing
... | true with Pool.step (Pool.beginClose order) (monitorPool s)
...   | just p′ = just (record s { monitorPool = p′ })
...   | nothing = nothing
step requestMonitorCancel s with Pool.step Pool.requestCancel (monitorPool s)
... | just p′ = just (record s { monitorPool = p′ })
... | nothing = nothing
step joinMonitor s with Pool.step Pool.join (monitorPool s)
... | just p′ = just (record s { monitorPool = p′ })
... | nothing = nothing
step finishMonitorClose s with Pool.step Pool.finishClose (monitorPool s)
... | just p′ = just (record s { monitorPool = p′ })
... | nothing = nothing
step (deliverMonitorCancellation err) s = deliverMonitor false err s
step (deliverBlockedMonitorCancellation err) s = deliverMonitor true err s
step (monitorBodyUnwound tid) s with lookup tid (monitors s)
... | just t with pc t | interrupted t
...   | cancelling | just f with Cancel.pc f
...     | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound tid) (monitorPool s)
...       | just p′ = just (record (finishPeer false (peerRef t) s)
  { monitorPool = p′; monitors = put tid (record t { pc = exited }) (monitors s) })
...       | nothing = nothing
step (monitorBodyUnwound tid) s | just t | cancelling | just f | _ = nothing
step (monitorBodyUnwound tid) s | just t | _ | _ = nothing
step (monitorBodyUnwound tid) s | nothing = nothing
step (deregisterMonitor tid) s with Pool.step (Pool.deregister tid) (monitorPool s)
... | just p′ = just (record s { monitorPool = p′ })
... | nothing = nothing
step (publishMonitorResult tid) s with Pool.step (Pool.publishAsyncResult tid) (monitorPool s)
... | just p′ = just (record s { monitorPool = p′ })
... | nothing = nothing

-- These three scope components are modeled here; CM/handler/server scope
-- completion is deliberately absent until the remaining supervision work.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
