{-# OPTIONS --guardedness #-}

-- Physical mini-protocol generations in the SAME queued pool as muxer/demuxer.
-- Responder commits/publications are actual outbound-machine writes. Initiator
-- fork is an observed source miniProtocolJob boundary; its local result cells
-- and typed pool are new components, not a claim about the old PSA frontend.
module ConnectionManagement.MuxProtocolJobs where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as Nat
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (job)
open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.MuxJobTypes as Types
open Types using (TypedResult; Role; ProtocolJob)
import ConnectionManagement.MuxHandlerSupervision as Handler
module U = Handler TypedResult
module Startup = U.Startup
module Pool = Startup.Pool

record State : Set where
  constructor protocolState
  field base : U.State
        jobs : Store JobId ProtocolJob
        -- Exactly the append order of responder source finishedJobs occurrences.
        -- Initiator outcomes do not occupy an ordinal in that legacy table.
        pending : Store WorkerId (List JobId)
open State public
source : State → O.Configuration
source s = U.source (base s)
setSource : O.Configuration → State → State
setSource c s = record s { base = U.setSource c (base s) }
poolAt : WorkerId → State → Pool.State
poolAt w s = Startup.pool (U.startupAt w (base s))
setPool : WorkerId → U.Frame → Pool.State → State → State
setPool w f p s = record s { base = U.setFrame w
  (record f { startup = record (U.startup f) { pool = p } }) (base s) }
initial : O.Configuration → Maybe State
initial c with U.initial c
... | nothing = nothing
... | just u = just (protocolState u [] [])

muxAt : MuxId → State → Maybe M.Mux
muxAt mid s = lookup mid (IG.muxes (IG.execution (Machine.inboundGovernor (O.core (source s)))))
monitoring : U.Frame → Bool
monitoring f with Startup.phase (U.startup f)
... | Startup.monitoring _ _ = true
... | _ = false
noParent : Pool.State → Bool
noParent p with Pool.parentFork p
... | nothing = true
... | just _ = false
noResults : Pool.State → Bool
noResults p with Pool.completions p
... | [] = true
... | _ ∷ _ = false
sameDirection : M.JobDirection → M.JobDirection → Bool
sameDirection M.initiatorJob M.initiatorJob = true
sameDirection M.responderJob M.responderJob = true
sameDirection _ _ = false
sameOutcome : RunResult → RunResult → Bool
sameOutcome clean clean = true
sameOutcome (errored e) (errored f) = does (ErrorId.errorNumber e Nat.≟ ErrorId.errorNumber f)
sameOutcome _ _ = false
isActive : Types.BodyPhase → Bool
isActive (Types.resultCaptured clean) = false
isActive _ = true
active : WorkerId → M.JobDirection → ℕ → Store JobId ProtocolJob → Bool
active w dir n [] = false
active w dir n ((_ , job) ∷ rest) with w ≟ Types.owner job
... | no _ = active w dir n rest
... | yes _ with sameDirection dir (Types.direction job) ∧ does (n Nat.≟ Types.protocolNumber job) ∧ isActive (Types.phase job)
...   | true = true
...   | false = active w dir n rest
generationFresh : RunId → Store JobId ProtocolJob → Bool
generationFresh gen [] = true
generationFresh gen ((_ , job) ∷ rest) with gen ≟ Types.generation job
... | yes _ = false
... | no _ = generationFresh gen rest
fresh : JobId → RunId → State → Bool
fresh j gen s with lookup j (jobs s)
... | just _ = false
... | nothing = U.jobFresh j (U.frames (base s)) ∧ generationFresh gen (jobs s)

-- Inherited startup can still create/register infrastructure, but arbitrary
-- Result inputs and raw monitor/job operations cannot bypass this typed layer.
rawIGAllowed : IG.IGAction → Bool
rawIGAllowed action with Life.muxAction action
... | nothing = true
... | just _ = false
inheritedAllowed : U.Action → Bool
inheritedAllowed (U.startupStep _ (Startup.child _)) = false
inheritedAllowed (U.run (B.handler (H.run (Machine.igStep action)))) = rawIGAllowed action
inheritedAllowed _ = true
inherit : U.Action → State → Maybe State
inherit action s with inheritedAllowed action
... | false = nothing
... | true with U.step action (base s)
...   | nothing = nothing
...   | just next = just (record s { base = next })

-- The source monitor is inside the masked fork/register operation until the
-- separate registration below; child completion/publication need not wait.
responderFork : WorkerId → JobId → RunId → State → Maybe State
responderFork w j gen s with lookup w (U.frames (base s)) | fresh j gen s
... | just f | true with U.progress f | monitoring f
...   | U.promisePublished hid mid | true with muxAt mid s
...     | just m with M.callback m
...       | M.forkPending n with active w M.responderJob n (jobs s)
...         | false with O.advance (O.inbound (Machine.igStep (IG.forkResponder mid))) (source s) |
  Pool.step (Pool.fork j) (poolAt w s)
...           | just c | just p = just (record (setPool w f p (setSource c s))
  { jobs = put j (Types.protocolJob w mid M.responderJob n gen Types.executing) (jobs s) })
...           | _ | _ = nothing
responderFork w j gen s | just f | true | U.promisePublished hid mid | true | just m | M.forkPending n | true = nothing
responderFork w j gen s | just f | true | U.promisePublished hid mid | true | just m | _ = nothing
responderFork w j gen s | just f | true | U.promisePublished hid mid | true | nothing = nothing
responderFork w j gen s | just f | true | _ | _ = nothing
responderFork w j gen s | _ | _ = nothing

-- An observed actual initiator fork is deliberately distinct from the old
-- PeerActions.startProtocol flag. The contract supplies its source fork event;
-- this prefix does not implement command creation, result actions or PSA cells.
-- Known queued results/commands have priority over this unselected fork event.
initiatorFork : WorkerId → JobId → RunId → ℕ → State → Maybe State
initiatorFork w j gen n s with lookup w (U.frames (base s)) | fresh j gen s
... | just f | true with U.progress f | monitoring f | M.findProtocol n (U.bundle f)
...   | U.promisePublished hid mid | true | just descriptor with muxAt mid s
...     | just m with M.status m | M.callback m | M.commands m | noResults (poolAt w s) | active w M.initiatorJob n (jobs s)
...       | M.ready | M.returned | [] | true | false with Pool.step (Pool.fork j) (poolAt w s)
...         | just p = just (record (setPool w f p s)
  { jobs = put j (Types.protocolJob w mid M.initiatorJob n gen Types.executing) (jobs s) })
...         | nothing = nothing
initiatorFork w j gen n s | just f | true | U.promisePublished hid mid | true | just descriptor | just m | _ | _ | _ | _ | _ = nothing
initiatorFork w j gen n s | just f | true | U.promisePublished hid mid | true | just descriptor | nothing = nothing
initiatorFork w j gen n s | just f | true | _ | _ | _ = nothing
initiatorFork w j gen n s | _ | _ = nothing

register : JobId → State → Maybe State
register j s with lookup j (jobs s)
... | nothing = nothing
... | just job with lookup (Types.owner job) (U.frames (base s)) | Pool.parentFork (poolAt (Types.owner job) s)
...   | just f | just current with j ≟ current
...     | yes _ with Pool.step Pool.register (poolAt (Types.owner job) s)
...       | just p = just (setPool (Types.owner job) f p s)
...       | nothing = nothing
register j s | just job | just f | just current | no _ = nothing
register j s | just job | _ | _ = nothing

pendingAt : WorkerId → State → List JobId
pendingAt w s with lookup w (pending s)
... | nothing = []
... | just js = js
appendPending : ProtocolJob → JobId → State → State
appendPending job j s with Types.direction job
... | M.initiatorJob = s
... | M.responderJob = record s { pending = put (Types.owner job) (pendingAt (Types.owner job) s ++ (j ∷ [])) (pending s) }
returned : JobId → State → Maybe State
returned j s with lookup j (jobs s)
... | just job with Types.phase job
...   | Types.executing = just (record s { jobs = put j (record job { phase = Types.waitingEgress }) (jobs s) })
...   | _ = nothing
returned j s | nothing = nothing
canCapture : Types.BodyPhase → Bool
canCapture Types.executing = true
canCapture Types.waitingEgress = true
canCapture _ = false
capturedResult : ProtocolJob → RunResult → TypedResult
capturedResult job result = Types.protocolCompletion (Types.direction job) (Types.protocolNumber job) (Types.generation job) result

-- Responder commit is the actual completion/status STM. The physical thread
-- can still be running after that commit; its later jobAction/jobHandler return
-- is a separate observation below. Initiator cells are new metadata.
bodySource : ProtocolJob → RunResult → State → Maybe O.Configuration
bodySource job result s with Types.direction job
... | M.initiatorJob = just (source s)
... | M.responderJob = O.advance (O.inbound (Machine.igStep
  (IG.finishProtocol (Types.mux job) (Types.protocolNumber job) result))) (source s)
capture : JobId → ProtocolJob → RunResult → State → Maybe State
capture j job result s with lookup (Types.owner job) (U.frames (base s)) |
  lookup j (Pool.handles (poolAt (Types.owner job) s))
... | just f | just Pool.bodyRunning with bodySource job result s
...   | just c = just (appendPending job j (record (setSource c s)
  { jobs = put j (record job { phase = Types.resultCaptured result }) (jobs s) }))
...   | nothing = nothing
capture j job result s | _ | _ = nothing
cleanCommit : JobId → State → Maybe State
cleanCommit j s with lookup j (jobs s)
... | just job with Types.phase job
...   | Types.waitingEgress = capture j job clean s
...   | _ = nothing
cleanCommit j s | nothing = nothing
syncError : JobId → ErrorId → State → Maybe State
syncError j err s with lookup j (jobs s)
... | just job with canCapture (Types.phase job)
...   | true = capture j job (errored err) s
...   | false = nothing
syncError j err s | nothing = nothing

-- miniProtocolJob returns after its completion/status transaction (or after
-- its synchronous exception handler published the local error). Preserve that
-- unmasked window: clean can free the slot while this handle is bodyRunning.
-- Kernel guards make this return observation once-only and prevent publication
-- after cancellation, until a future explicit unwind model handles that case.
returnBody : JobId → State → Maybe State
returnBody j s with lookup j (jobs s)
... | nothing = nothing
... | just job with Types.phase job | lookup (Types.owner job) (U.frames (base s))
...   | Types.resultCaptured result | just f with Pool.step
  (Pool.bodyReturnedWith j (capturedResult job result)) (poolAt (Types.owner job) s)
...     | just p = just (setPool (Types.owner job) f p s)
...     | nothing = nothing
returnBody j s | just job | _ | _ = nothing

-- The ordinal is a physical identity's location in RESPONDER append order.
-- Removing that occurrence permits a newer same-number generation to publish
-- before an older completed thread, while retaining the older pending result.
locate : JobId → List JobId → Maybe (ℕ × List JobId)
locate j [] = nothing
locate j (k ∷ rest) with j ≟ k
... | yes _ = just (zero , rest)
... | no _ with locate j rest
...   | nothing = nothing
...   | just (i , kept) = just (suc i , k ∷ kept)
resultMatches : ProtocolJob → RunResult → TypedResult → Bool
resultMatches job outcome (Types.protocolCompletion dir n gen result) =
  sameDirection (Types.direction job) dir ∧ does (Types.protocolNumber job Nat.≟ n) ∧
  does (Types.generation job ≟ gen) ∧ sameOutcome outcome result
resultMatches _ _ _ = false

-- Event matching compares BOTH the captured physical value and selected source
-- occurrence. It is not a global validity predicate or a number-only removal.
publicationSource : JobId → ProtocolJob → RunResult → State → Maybe (O.Configuration × List JobId)
publicationSource j job outcome s with Types.direction job
... | M.initiatorJob = just (source s , pendingAt (Types.owner job) s)
... | M.responderJob with locate j (pendingAt (Types.owner job) s) | muxAt (Types.mux job) s
...   | just (i , kept) | just m with IG.takePending i (M.finishedJobs m)
...     | just ((n , result) , rest) with does (Types.protocolNumber job Nat.≟ n) ∧ sameOutcome outcome result
...       | true with O.advance (O.inbound (Machine.igStep (IG.publishJobOccurrence (Types.mux job) i))) (source s)
...         | just c = just (c , kept)
...         | nothing = nothing
publicationSource j job outcome s | M.responderJob | just (i , kept) | just m | just ((n , result) , rest) | false = nothing
publicationSource j job outcome s | M.responderJob | just (i , kept) | just m | nothing = nothing
publicationSource j job outcome s | M.responderJob | _ | _ = nothing
removePublished : ProtocolJob → List JobId → State → State
removePublished job kept s with Types.direction job
... | M.initiatorJob = s
... | M.responderJob = record s { pending = put (Types.owner job) kept (pending s) }
publish : JobId → State → Maybe State
publish j s with lookup j (jobs s)
... | nothing = nothing
... | just job with Types.phase job | lookup (Types.owner job) (U.frames (base s)) | lookup j (Pool.handles (poolAt (Types.owner job) s))
...   | Types.resultCaptured result | just f | just (Pool.bodyReturned value) with resultMatches job result value
...     | true with publicationSource j job result s | Pool.step (Pool.publishCompletion j) (poolAt (Types.owner job) s)
...       | just (c , kept) | just p = just (removePublished job kept (setPool (Types.owner job) f p (setSource c s)))
...       | _ | _ = nothing
publish j s | just job | Types.resultCaptured result | just f | just (Pool.bodyReturned value) | false = nothing
publish j s | just job | _ | _ | _ = nothing

-- Deregistration and Async result availability are independent of queue
-- publication and remain possible after another generation has started.
viaProtocol : JobId → Pool.Action → State → Maybe State
viaProtocol j action s with lookup j (jobs s)
... | nothing = nothing
... | just job with lookup (Types.owner job) (U.frames (base s)) | Pool.step action (poolAt (Types.owner job) s)
...   | just f | just p = just (setPool (Types.owner job) f p s)
...   | _ | _ = nothing

-- Infrastructure identities are exposed as soon as each fork occurs, so fast
-- child completion/publication is possible inside the masked insertion gap.
infraId : Role → Startup.PC → Maybe JobId
infraId Types.muxer (Startup.muxerForked m) = just m
infraId Types.muxer (Startup.muxerRegistered m) = just m
infraId Types.muxer (Startup.demuxerForked m d) = just m
infraId Types.muxer (Startup.demuxerRegistered m d) = just m
infraId Types.muxer (Startup.matureTraced m d) = just m
infraId Types.muxer (Startup.monitoring m d) = just m
infraId Types.demuxer (Startup.demuxerForked m d) = just d
infraId Types.demuxer (Startup.demuxerRegistered m d) = just d
infraId Types.demuxer (Startup.matureTraced m d) = just d
infraId Types.demuxer (Startup.monitoring m d) = just d
infraId _ _ = nothing
viaInfra : WorkerId → Role → (JobId → Pool.Action) → State → Maybe State
viaInfra w role action s with lookup w (U.frames (base s))
... | nothing = nothing
... | just f with infraId role (Startup.phase (U.startup f))
...   | nothing = nothing
...   | just j with Pool.step (action j) (poolAt w s)
...     | nothing = nothing
...     | just p = just (setPool w f p s)

-- These are the only permitted source-monitor controls in this prefix. Once a
-- start command is selected, its tracer/fork continuation may finish despite a
-- newly queued result; selecting a new command/demand must respect that queue.
data MonitorAction : Set where
  selectCommand sampleTracer commitTracer finishStart : MonitorAction
  demand : ℕ → MonitorAction
sourceControl : MonitorAction → MuxId → IG.IGAction
sourceControl selectCommand mid = IG.monitorCommand mid
sourceControl sampleTracer mid = IG.sampleTracer mid
sourceControl commitTracer mid = IG.commitTracer mid
sourceControl finishStart mid = IG.finishStart mid
sourceControl (demand n) mid = IG.startOnDemand mid n
controlReady : MonitorAction → M.Mux → Pool.State → Bool
controlReady selectCommand m p with M.status m | M.callback m | M.commands m
... | M.ready | M.returned | M.startCommand _ ∷ _ = noResults p
... | _ | _ | _ = false
controlReady (demand n) m p = noResults p
controlReady _ m p = true
monitorControl : WorkerId → MonitorAction → State → Maybe State
monitorControl w action s with lookup w (U.frames (base s))
... | nothing = nothing
... | just f with U.progress f | monitoring f | noParent (poolAt w s)
...   | U.promisePublished hid mid | true | true with muxAt mid s
...     | nothing = nothing
...     | just m with controlReady action m (poolAt w s)
...       | false = nothing
...       | true with O.advance (O.inbound (Machine.igStep (sourceControl action mid))) (source s)
...         | nothing = nothing
...         | just c = just (setSource c s)
monitorControl w action s | just f | _ | _ | _ = nothing

data Action : Set where
  run : U.Action → Action
  forkResponder : WorkerId → JobId → RunId → Action
  forkInitiator : WorkerId → JobId → RunId → ℕ → Action
  registerProtocol protocolReturned commitClean returnProtocol publishProtocol deregisterProtocol asyncProtocolResult : JobId → Action
  protocolException : JobId → ErrorId → Action
  infrastructureReturn : WorkerId → Role → ErrorId → Action
  publishInfra deregisterInfra asyncInfraResult : WorkerId → Role → Action
  control : WorkerId → MonitorAction → Action
step : Action → State → Maybe State
step (run action) s = inherit action s
step (forkResponder w j gen) s = responderFork w j gen s
step (forkInitiator w j gen n) s = initiatorFork w j gen n s
step (registerProtocol j) s = register j s
step (protocolReturned j) s = returned j s
step (commitClean j) s = cleanCommit j s
step (protocolException j err) s = syncError j err s
step (returnProtocol j) s = returnBody j s
step (publishProtocol j) s = publish j s
step (deregisterProtocol j) s = viaProtocol j (Pool.deregister j) s
step (asyncProtocolResult j) s = viaProtocol j (Pool.publishAsyncResult j) s
step (infrastructureReturn w role err) s = viaInfra w role (λ j → Pool.bodyReturnedWith j (Types.infraResult role err)) s
step (publishInfra w role) s = viaInfra w role Pool.publishCompletion s
step (deregisterInfra w role) s = viaInfra w role Pool.deregister s
step (asyncInfraResult w role) s = viaInfra w role Pool.publishAsyncResult s
step (control w action) s = monitorControl w action s

-- No result-consumption, group-close, cancel/unwind, or join operation is
-- exposed. The typed physical queue is authoritative; the old source queue is
-- only its responder projection, pending a future typed monitor/frontend bridge.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
