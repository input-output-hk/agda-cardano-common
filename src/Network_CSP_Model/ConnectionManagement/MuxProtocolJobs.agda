{-# OPTIONS --guardedness #-}

-- Physical mini-protocol generations in the SAME queued pool as muxer/demuxer.
-- Responder commits/publications are actual outbound-machine writes. Initiator
-- fork is an observed source miniProtocolJob boundary; its local result cells
-- and typed pool are new components, not a claim about the old PSA frontend.
module ConnectionManagement.MuxProtocolJobs where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as Nat
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
import ConnectionManagement.Rules.MuxEgress as EgressKernel
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
-- Physical JobId supplies the particular child buffer identity. Freshness of
-- that child is checked by the real pool fork; shared key cells are not reset.
jobKey : ProtocolJob → M.ProtocolKey
jobKey job = Types.protocolNumber job , Types.direction job
wantonMatches : JobId → ProtocolJob → M.Mux → Bool
wantonMatches j job m with lookup (serial j) (M.Egress.wantons (M.egress m))
... | nothing = false
... | just want with M.Egress.key want ≟ jobKey job
...   | yes _ = true
...   | no _ = false
hasWanton : JobId → ProtocolJob → State → Bool
hasWanton j job s with muxAt (Types.mux job) s
... | nothing = false
... | just m = wantonMatches j job m
cleanReady : JobId → ProtocolJob → State → Bool
cleanReady j job s with muxAt (Types.mux job) s
... | nothing = false
... | just m = wantonMatches j job m ∧ M.Egress.protocolReady (serial j) (M.egress m)

-- Allocation is the first child jobAction operation, after actual birth but
-- independent of the masked parent's registry insertion. A cancelled child
-- cannot allocate or send after its Pool.bodyRunning observation is lost.
protocolEgress : JobId → (ProtocolJob → M.Egress.Action) → State → Maybe State
protocolEgress j action s with lookup j (jobs s)
... | nothing = nothing
... | just job with Types.phase job | lookup (Types.owner job) (U.frames (base s)) |
  lookup j (Pool.handles (poolAt (Types.owner job) s))
...   | Types.executing | just f | just Pool.bodyRunning with O.advance
  (O.inbound (Machine.igStep (IG.egressStep (Types.mux job) (action job)))) (source s)
...     | nothing = nothing
...     | just next = just (setSource next s)
protocolEgress j action s | just job | _ | _ | _ = nothing
enterProtocol : JobId → State → Maybe State
enterProtocol j = protocolEgress j (λ job → M.Egress.createWanton (serial j) (jobKey job))
sendProtocol : JobId → ℕ → State → Maybe State
sendProtocol j bytes s with lookup j (jobs s)
... | nothing = nothing
... | just job with hasWanton j job s
...   | false = nothing
...   | true = protocolEgress j (λ _ → M.Egress.appendPayload (serial j) bytes) s

-- Monitor entry after the legacy or the complete configured startup.
monitoring : U.Frame → Bool
monitoring f = Startup.monitoringPC (Startup.phase (U.startup f))
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
-- Source runMiniProtocolSTM selects an existing number/direction state;
-- lack of support prevents the physical child fork, not only its later send.
configuredKey : M.JobDirection → ℕ → M.Mux → Bool
configuredKey dir n m with lookup (n , dir) (M.Egress.cells (M.egress m))
... | nothing = false
... | just _ = true
forkBlocked : WorkerId → M.JobDirection → ℕ → Store JobId ProtocolJob → M.Mux → Bool
forkBlocked w dir n js m = active w dir n js ∨ not (configuredKey dir n m)
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
...       | M.forkPending n with forkBlocked w M.responderJob n (jobs s) m
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
...     | just m with M.status m | M.callback m | M.commands m | noResults (poolAt w s) | forkBlocked w M.initiatorJob n (jobs s) m
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
...   | Types.executing with hasWanton j job s
...     | false = nothing
...     | true = just (record s { jobs = put j (record job { phase = Types.waitingEgress }) (jobs s) })
returned j s | just job | _ = nothing
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
...   | Types.waitingEgress with cleanReady j job s
...     | false = nothing
...     | true = capture j job clean s
cleanCommit j s | just job | _ = nothing
cleanCommit j s | nothing = nothing
syncError : JobId → ErrorId → State → Maybe State
syncError j err s with lookup j (jobs s)
... | just job with canCapture (Types.phase job)
...   | true = capture j job (errored err) s
...   | false = nothing
syncError j err s | nothing = nothing

dbEngine : State → IG.Engine
dbEngine s = IG.execution (Machine.inboundGovernor (O.core (source s)))
-- A collector blocked in a LeiosDB await (consensus processLeiosBlock and
-- ingestAcquiredTxs) cannot send or return from its body until the await ends.
awaitingDb : JobId → State → Bool
awaitingDb j s with lookup j (IG.dbWaits (dbEngine s))
... | nothing = false
... | just _ = true
unlessAwaiting : JobId → State → Maybe State → Maybe State
unlessAwaiting j s r with awaitingDb j s
... | true = nothing
... | false = r
-- Proof adapter: a step admitted by the await guard is the unguarded step.
unlessAwaiting-just : ∀ j s r {t} → unlessAwaiting j s r ≡ just t → r ≡ just t
unlessAwaiting-just j s r eq with lookup j (IG.dbWaits (dbEngine s))
... | nothing = eq
unlessAwaiting-just j s r () | just _
-- Only a running, uncommitted body can submit to or await the DB queue.
collector : JobId → State → Maybe ProtocolJob
collector j s with lookup j (jobs s)
... | nothing = nothing
... | just job with Types.phase job | lookup (Types.owner job) (U.frames (base s)) |
  lookup j (Pool.handles (poolAt (Types.owner job) s))
...   | Types.executing | just f | just Pool.bodyRunning = just job
...   | _ | _ | _ = nothing
viaDb : IG.DbAction → State → Maybe State
viaDb a s with O.advance (O.inbound (Machine.igStep (IG.leiosDb a))) (source s)
... | nothing = nothing
... | just c = just (setSource c s)
submitDb : JobId → ℕ → State → Maybe State
submitDb j d s with collector j s
... | nothing = nothing
... | just _ = viaDb (IG.submitWrite j d) s
awaitDb : JobId → State → Maybe State
awaitDb j s with collector j s
... | nothing = nothing
... | just _ = viaDb (IG.takeResult j) s
-- The await (or a submission to the sealed queue) throws the seal cause in the
-- collector; its existing synchronous handler captures that error. Wrapping
-- the cause into LeiosDbWriteException is abstracted to the same ErrorId.
dbFailure : JobId → State → Maybe State
dbFailure j s with collector j s | IG.dbSealed (dbEngine s)
... | just job | just err with awaitingDb j s
...   | false = syncError j err s
...   | true with viaDb (IG.abandonWait j) s
...     | nothing = nothing
...     | just next = syncError j err next
dbFailure j s | _ | _ = nothing

-- Proof adapters: every DB action is a source step, possibly followed by the
-- existing synchronous-error capture.
viaDb-source : ∀ a s {t} → viaDb a s ≡ just t →
  Σ O.Configuration (λ c → O.advance (O.inbound (Machine.igStep (IG.leiosDb a))) (source s) ≡ just c × setSource c s ≡ t)
viaDb-source a s eq with O.advance (O.inbound (Machine.igStep (IG.leiosDb a))) (source s)
viaDb-source a s refl | just c = c , refl , refl
submitDb-via : ∀ j d s {t} → submitDb j d s ≡ just t → viaDb (IG.submitWrite j d) s ≡ just t
submitDb-via j d s eq with collector j s
submitDb-via j d s eq | just _ = eq
awaitDb-via : ∀ j s {t} → awaitDb j s ≡ just t → viaDb (IG.takeResult j) s ≡ just t
awaitDb-via j s eq with collector j s
awaitDb-via j s eq | just _ = eq
data DbFailure (j : JobId) (s t : State) : Set where
  refused : ∀ err → syncError j err s ≡ just t → DbFailure j s t
  abandoned : ∀ err mid → viaDb (IG.abandonWait j) s ≡ just mid → syncError j err mid ≡ just t → DbFailure j s t
dbFailure-via : ∀ j s {t} → dbFailure j s ≡ just t → DbFailure j s t
dbFailure-via j s eq with collector j s | IG.dbSealed (dbEngine s)
... | just job | just err with awaitingDb j s
...   | false = refused err eq
...   | true with viaDb (IG.abandonWait j) s in abandon
...     | just next = abandoned err next abandon eq

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
infraId = Startup.roleId
viaInfra : WorkerId → Role → (JobId → Pool.Action) → State → Maybe State
viaInfra w role action s with lookup w (U.frames (base s))
... | nothing = nothing
... | just f with infraId role (Startup.phase (U.startup f))
...   | nothing = nothing
...   | just j with Pool.step (action j) (poolAt w s)
...     | nothing = nothing
...     | just p = just (setPool w f p s)

-- Only the actual lane muxer can consume/build/write its batch. Create/send
-- actions belong to protocol children and have no infrastructure alias here.
-- The role is derived from the actual mux layout and the batch's lane, then
-- resolved through the actual historical startup binding (legacy or configured).
batchLane : ℕ → M.Egress.State → Maybe EgressKernel.Lane
batchLane id e with lookup id (M.Egress.batches e)
... | nothing = nothing
... | just b = just (M.Egress.lane b)
egressLane : M.Egress.Action → M.Egress.State → Maybe EgressKernel.Lane
egressLane (M.Egress.createWanton _ _) _ = nothing
egressLane (M.Egress.appendPayload _ _) _ = nothing
egressLane (M.Egress.takeFirst lane) _ = just lane
egressLane (M.Egress.selectDemand id) e = batchLane id e
egressLane (M.Egress.takeFragment id) e = batchLane id e
egressLane (M.Egress.finishBatch id) e = batchLane id e
egressLane (M.Egress.writeAccount id) e = batchLane id e
egressLane (M.Egress.writeFailed id) e = batchLane id e
egressLane (M.Egress.advance id _) e = batchLane id e
laneWorker : U.Frame → M.Egress.Action → State → Maybe (MuxId × JobId)
laneWorker f action s with U.progress f
... | U.promisePublished hid mid with muxAt mid s
...   | nothing = nothing
...   | just m with egressLane action (M.egress m)
...     | nothing = nothing
...     | just lane with Types.roleForLane (M.Egress.layout (M.egress m)) lane
...       | nothing = nothing
...       | just role with infraId role (Startup.phase (U.startup f))
...         | nothing = nothing
...         | just j = just (mid , j)
laneWorker f action s | _ = nothing
muxerEgress : WorkerId → M.Egress.Action → State → Maybe State
muxerEgress w action s with lookup w (U.frames (base s))
... | nothing = nothing
... | just f with laneWorker f action s
...   | nothing = nothing
...   | just (mid , j) with lookup j (Pool.handles (poolAt w s))
...     | just Pool.bodyRunning with O.advance (O.inbound (Machine.igStep (IG.egressStep mid action))) (source s)
...       | nothing = nothing
...       | just next = just (setSource next s)
muxerEgress w action s | just f | just (mid , j) | _ = nothing

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
  enterProtocolBody : JobId → Action
  appendProtocolPayload : JobId → ℕ → Action
  egressMuxer : WorkerId → M.Egress.Action → Action
  registerProtocol protocolReturned commitClean returnProtocol publishProtocol deregisterProtocol asyncProtocolResult : JobId → Action
  protocolException : JobId → ErrorId → Action
  infrastructureReturn : WorkerId → Role → ErrorId → Action
  publishInfra deregisterInfra asyncInfraResult : WorkerId → Role → Action
  control : WorkerId → MonitorAction → Action
  -- Collector-owned LeiosDB waits and the node-owned writer thread.
  submitDbWrite : JobId → ℕ → Action
  awaitDbWrite dbWriteFailed : JobId → Action
  writerComplete : ℕ → Action
  writerSeal : ErrorId → Action
step : Action → State → Maybe State
step (run action) s = inherit action s
step (forkResponder w j gen) s = responderFork w j gen s
step (forkInitiator w j gen n) s = initiatorFork w j gen n s
step (enterProtocolBody j) s = enterProtocol j s
step (appendProtocolPayload j bytes) s = unlessAwaiting j s (sendProtocol j bytes s)
step (egressMuxer w action) s = muxerEgress w action s
step (registerProtocol j) s = register j s
step (protocolReturned j) s = unlessAwaiting j s (returned j s)
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
step (submitDbWrite j d) s = submitDb j d s
step (awaitDbWrite j) s = awaitDb j s
step (dbWriteFailed j) s = dbFailure j s
step (writerComplete d) s = viaDb (IG.completeWrite d) s
step (writerSeal err) s = viaDb (IG.sealQueue err) s

-- No result-consumption, group-close, cancel/unwind, or join operation is
-- exposed. The typed physical queue is authoritative; the old source queue is
-- only its responder projection, pending a future typed monitor/frontend bridge.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
