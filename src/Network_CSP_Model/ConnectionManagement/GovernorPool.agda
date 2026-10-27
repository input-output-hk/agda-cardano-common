{-# OPTIONS --guardedness #-}

-- Governor-owned jobs coupled to the shared subsystem and real caller unwind.
-- This is one supervision scope, not the outer monitor/handler/server scopes.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)

module ConnectionManagement.GovernorPool (isIOManagerError : ErrorId → Bool) where
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put; delete)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.JobPoolLifecycle as Lifecycle
module Production = Policy.Profile isIOManagerError

-- Jitter remains an input to actual enqueue; this ledger preserves its exact
-- job identity, captured arguments and outcome without inventing another result.
record Body : Set where
  constructor body
  field identity : JobId
        work : G.Job
        outcome : G.Outcome
open Body public
module Pool = Lifecycle Body

record State : Set where
  constructor supervised
  field source : Policy.State
        pool : Pool.State
        regions : Store WorkerId Cancel.Context
        unwinding : Store JobId Cancel.Frame
open State public

initial : CM.Configuration → G.State → State
initial c g = supervised (Production.initial (Sub.initial c g)) Pool.initial [] []

machine : State → Sub.Configuration
machine s = Policy.machine (source s)
cm : State → CM.Configuration
cm s = J.cm (Sub.world (machine s))
setCM : CM.Configuration → State → State
setCM c s = record s { source = record (source s)
  { machine = record (machine s) { world = record (Sub.world (machine s)) { cm = c } } } }

-- Counts have ordinary and protected-cleanup origins, so retain their region.
region : WorkerId → State → Cancel.Context
region w s with lookup w (regions s)
... | nothing = Cancel.ordinary
... | just context = context

sameKind : G.Kind → G.Kind → Bool
sameKind G.forget G.forget = true
sameKind G.establish G.establish = true
sameKind G.activate G.activate = true
sameKind G.close G.close = true
sameKind G.deactivate G.deactivate = true
sameKind _ _ = false
sameCapture : Maybe PeerConnectionId → Maybe PeerConnectionId → Bool
sameCapture nothing nothing = true
sameCapture (just a) (just b) = does (a ≟ b)
sameCapture _ _ = false
sameJob : G.Job → G.Job → Bool
sameJob a b = sameKind (G.kind a) (G.kind b) ∧ does (G.peer a ≟ G.peer b) ∧
  sameCapture (G.captured a) (G.captured b)
sameOutcome : G.Outcome → G.Outcome → Bool
sameOutcome G.succeeded G.succeeded = true
sameOutcome G.failed G.failed = true
sameOutcome G.demotionTimedOut G.demotionTimedOut = true
sameOutcome (G.establishedOK a) (G.establishedOK b) = does (a ≟ b)
sameOutcome _ _ = false

-- A source completion cannot differ from the captured body's return value.
returnedBody : JobId → Sub.Configuration → Body → Bool
returnedBody j c captured with lookup j (Sub.jobs c)
... | nothing = false
... | just jf with J.pc (Sub.execution jf)
...   | J.complete result = does (j ≟ identity captured) ∧
  sameJob (J.work (Sub.execution jf)) (work captured) ∧ sameOutcome result (outcome captured)
...   | _ = false

running : JobId → Pool.State → Bool
running j p with lookup j (Pool.handles p)
... | just Pool.bodyRunning = true
... | _ = false

-- Only the spawning governor stops at its lexical pool-close boundary. Other
-- workers, peer monitors, IG and handler actions may still run.
ownerOpen : Pool.State → Bool
ownerOpen p with Pool.phase p
... | Pool.openPool = true
... | _ = false
ownerAction : Sub.Action → Bool
ownerAction Sub.publishPublicState = true
ownerAction (Sub.sampleTime _) = true
ownerAction (Sub.applyAt _) = true
ownerAction (Sub.selectMonitor _) = true
ownerAction Sub.selectCompletion = true
ownerAction Sub.selectTargets = true
ownerAction Sub.selectWakeup = true
ownerAction Sub.registerWakeup = true
ownerAction Sub.expireWakeup = false
ownerAction Sub.cancelWakeup = true
ownerAction Sub.publishCounters = true
ownerAction Sub.traceSelection = true
ownerAction (Sub.selectPolicy _) = true
ownerAction Sub.finishLaunch = true
ownerAction _ = false

-- A terminated or unwinding governor child cannot resume its original CM call.
workerRunning : WorkerId → Store JobId Sub.JobFrame → Pool.State → Bool
workerRunning w [] p = true
workerRunning w ((j , jf) ∷ rest) p with w ≟ J.caller (Sub.execution jf)
... | yes _ = running j p
... | no _ = workerRunning w rest p
-- An owned caller starts CM operations through its job continuation, not an
-- independent environment begin that could overwrite the job's return cell.
unowned : WorkerId → Store JobId Sub.JobFrame → Bool
unowned w [] = true
unowned w ((_ , jf) ∷ rest) with w ≟ J.caller (Sub.execution jf)
... | yes _ = false
... | no _ = unowned w rest
coreAllowed : CM.Action → State → Bool
coreAllowed (CM.beginAcquire w _) s = unowned w (Sub.jobs (machine s))
coreAllowed (CM.beginRelease w _) s = unowned w (Sub.jobs (machine s))
coreAllowed (CM.release w _) s = workerRunning w (Sub.jobs (machine s)) (pool s)
coreAllowed (CM.acquire w _) s with region w s
... | Cancel.forkedBeforeHandoff = false
... | _ = workerRunning w (Sub.jobs (machine s)) (pool s)
coreAllowed (CM.inbound _) s = true

-- Couple actual raw fork/register/queue/removal events; arbitrary pool inputs
-- cannot manufacture job results or deregister a live source continuation.
normalPool : Sub.Action → State → Maybe Pool.State
normalPool (Sub.forkJob _ _ _) s with ownerOpen (pool s)
... | true = Pool.step (Pool.fork (ident (Sub.nextJob (machine s)))) (pool s)
... | false = nothing
normalPool Sub.registerJob s with Sub.pc (machine s) | Pool.parentFork (pool s)
... | Sub.register j _ | just k with j ≟ k
...   | yes _ = Pool.step Pool.register (pool s)
...   | no _ = nothing
normalPool Sub.registerJob s | _ | _ = nothing
normalPool (Sub.enqueueCompletion j _) s with lookup j (Pool.handles (pool s))
... | just (Pool.bodyReturned captured) with returnedBody j (machine s) captured
...   | true = Pool.step (Pool.publishCompletion j) (pool s)
...   | false = nothing
normalPool (Sub.enqueueCompletion j _) s | _ = nothing
normalPool (Sub.deregisterJob j) s = Pool.step (Pool.deregister j) (pool s)
normalPool (Sub.jobStep j _) s with running j (pool s)
... | true = just (pool s)
... | false = nothing
normalPool (Sub.core action) s with coreAllowed action s
... | true = just (pool s)
... | false = nothing
normalPool action s with ownerAction action | ownerOpen (pool s)
... | true | false = nothing
... | _ | _ = just (pool s)

-- Capture completion in the same modeled transition as the job body returns;
-- no artificial interruptible gap is added before its masked publication.
noteReturn : Sub.Action → Sub.Configuration → Pool.State → Maybe Pool.State
noteReturn (Sub.jobStep j _) c p with lookup j (Sub.jobs c)
... | nothing = nothing
... | just jf with J.pc (Sub.execution jf)
...   | J.complete result = Pool.step (Pool.bodyReturnedWith j (body j (J.work (Sub.execution jf)) result)) p
...   | _ = just p
noteReturn _ c p = just p

-- Record the protected bracket and explicit handler-fork/handoff gap. Counts
-- inherit this context until the CM exception/return boundary has been crossed.
noteAcquire : WorkerId → A.Action → CM.Configuration → Store WorkerId Cancel.Context → Store WorkerId Cancel.Context
noteAcquire w A.returnResult c contexts = put w Cancel.ordinary contexts
noteAcquire w (A.closeFailed _) c contexts = put w Cancel.ordinary contexts
noteAcquire w A.forkOK c contexts = put w Cancel.forkedBeforeHandoff contexts
noteAcquire w action c contexts with lookup w (CM.acquiring c)
... | just f with A.pc f
...   | A.closeError _ _ = put w Cancel.protectedCleanup contexts
...   | A.removeError _ _ = put w Cancel.protectedCleanup contexts
...   | _ = contexts
noteAcquire w action c contexts | nothing = contexts
noteRegions : Sub.Action → CM.Configuration → Store WorkerId Cancel.Context → Store WorkerId Cancel.Context
noteRegions (Sub.core (CM.beginAcquire w _)) c contexts = put w Cancel.ordinary contexts
noteRegions (Sub.core (CM.acquire w action)) c contexts = noteAcquire w action c contexts
noteRegions _ c contexts = contexts

data Action : Set where
  run : Sub.Action → Action
  handoff : WorkerId → Action
  beginClose : List JobId → Action
  requestCancel join finishClose : Action
  deliverCancellation deliverOpenCancellation : ErrorId → Action
  cleanup : JobId → Cancel.Action → Action
  bodyUnwound recoverCloseFailure deregisterCancelled publishAsyncResult : JobId → Action

-- Establishment's outer bracket restores Cold only before its successful return.
restoreCold : J.Frame → Sub.Configuration → Sub.Configuration
restoreCold f c with G.kind (J.work f) | J.pc f
... | G.establish | J.begin = c
... | G.establish | J.complete _ = c
... | G.establish | _ with lookup (J.connectionRef f) (J.peers (Sub.world c))
...   | nothing = c
...   | just peer = record c { world = record (Sub.world c)
  { peers = put (J.connectionRef f) (record peer { status = Peer.peerCold }) (J.peers (Sub.world c)) } }
restoreCold f c | _ | _ = c

-- An explicit blocked-open observation is needed for masked acquisition.
deliveryContext : Bool → Cancel.Context → Cancel.Context
deliveryContext true Cancel.ordinary = Cancel.interruptibleOpen
deliveryContext false old = old
deliveryContext true old = Cancel.protectedCleanup

-- The current owner can deliver to only the pool cursor's captured handle.
deliver : Bool → ErrorId → State → Maybe State
deliver openBlocked err s with Pool.phase (pool s)
... | Pool.cancelPending j with lookup j (Sub.jobs (machine s)) | Pool.step Pool.deliverCancel (pool s)
...   | just jf | just p′ with Cancel.start (J.caller (Sub.execution jf)) err
    (deliveryContext openBlocked (region (J.caller (Sub.execution jf)) s)) (cm s)
...     | just (f , c′) = just (record (setCM c′ s)
  { pool = p′; unwinding = put j f (unwinding s) })
...     | nothing = nothing
deliver openBlocked err s | Pool.cancelPending j | _ | _ = nothing
deliver openBlocked err s | _ = nothing

step : Action → State → Maybe State
step (run action) s with normalPool action s | Production.step (Policy.dispatch action) (source s)
... | just p′ | just c′ with noteReturn action (Policy.machine c′) p′
...   | just p″ = just (supervised c′ p″
  (noteRegions action (J.cm (Sub.world (Policy.machine c′))) (regions s)) (unwinding s))
...   | nothing = nothing
step (run action) s | _ | _ = nothing
step (handoff w) s with region w s | lookup w (CM.acquiring (cm s))
... | Cancel.forkedBeforeHandoff | just f with A.pc f
...   | A.connectedCommit _ _ _ = just (record s { regions = put w Cancel.ordinary (regions s) })
...   | _ = nothing
step (handoff w) s | _ | _ = nothing
step (beginClose order) s with Pool.step (Pool.beginClose order) (pool s)
... | nothing = nothing
... | just p′ = just (record s { pool = p′ })
step requestCancel s with Pool.step Pool.requestCancel (pool s)
... | nothing = nothing
... | just p′ = just (record s { pool = p′ })
step join s with Pool.step Pool.join (pool s)
... | nothing = nothing
... | just p′ = just (record s { pool = p′ })
step finishClose s with Pool.step Pool.finishClose (pool s)
... | nothing = nothing
... | just p′ = just (record s { pool = p′ })
step (deliverCancellation err) s = deliver false err s
step (deliverOpenCancellation err) s = deliver true err s
step (cleanup j action) s with lookup j (unwinding s)
... | nothing = nothing
... | just f with Cancel.step action f (cm s)
...   | nothing = nothing
...   | just (f′ , c′) = just (record (setCM c′ s) { unwinding = put j f′ (unwinding s) })
step (bodyUnwound j) s with lookup j (unwinding s) | lookup j (Sub.jobs (machine s))
... | just f | just jf with Cancel.pc f
...   | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound j) (pool s)
...     | just p′ = just (record s { pool = p′; source = record (source s)
  { machine = restoreCold (Sub.execution jf) (machine s) } })
...     | nothing = nothing
step (bodyUnwound j) s | just f | just jf | Cancel.finished Cancel.cleanupComplete with Pool.step (Pool.bodyUnwound j) (pool s)
... | just p′ = just (record s { pool = p′; source = record (source s)
  { machine = restoreCold (Sub.execution jf) (machine s) } })
... | nothing = nothing
step (bodyUnwound j) s | just f | just jf | _ = nothing
step (bodyUnwound j) s | nothing | _ = nothing
step (bodyUnwound j) s | _ | nothing = nothing
-- A close exception overrides AsyncCancelled. Return that exception to PSA's
-- ordinary policy path, where it may fail the job or deliver a fatal exception.
step (recoverCloseFailure j) s with lookup j (unwinding s) | lookup j (Sub.jobs (machine s))
... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with Pool.step (Pool.resumeAfterUnwindError j) (pool s)
...     | just p′ = just (record (setCM (record (cm s)
    { acquired = put (Cancel.caller f) (Cases.raised (Cases.ioFailure err)) (CM.acquired (cm s)) }) s)
  { pool = p′; unwinding = delete j (unwinding s); regions = put (Cancel.caller f) Cancel.ordinary (regions s) })
...     | nothing = nothing
step (recoverCloseFailure j) s | just f | just jf | _ | _ | _ = nothing
step (recoverCloseFailure j) s | nothing | _ = nothing
step (recoverCloseFailure j) s | _ | nothing = nothing
step (deregisterCancelled j) s with lookup j (Sub.jobs (machine s)) | Pool.step (Pool.deregister j) (pool s)
... | just jf | just p′ with lookup j (Pool.handles (pool s))
...   | just (Pool.deregisterPending Pool.cancelledExit) = just (record s
  { pool = p′; source = record (source s) { machine = record (machine s)
    { jobs = put j (record jf { deregistered = true }) (Sub.jobs (machine s))
    ; pool = Pool.remove j (Sub.pool (machine s)) } } })
...   | _ = nothing
step (deregisterCancelled j) s | _ | _ = nothing
step (publishAsyncResult j) s with Pool.step (Pool.publishAsyncResult j) (pool s)
... | nothing = nothing
... | just p′ = just (record s { pool = p′ })

-- Finite coupled executions include actual CM cleanup writes, not raw stutters.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
