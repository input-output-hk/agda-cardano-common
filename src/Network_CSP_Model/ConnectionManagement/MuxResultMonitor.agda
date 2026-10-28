{-# OPTIONS --guardedness #-}

-- An ordered physical-result consumer over the existing typed mux pool.
-- isBearerClosed must project the source exception's dynamic BearerClosed
-- classification; exception IDs themselves do not establish that contract.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.MuxResultMonitor (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as Nat
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (job)
open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.MuxProtocolJobs as P
module U = P.U
module Startup = P.Startup
module Pool = P.Pool
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O

data Finish : Set where
  normal : Finish
  failed : ErrorId → Finish
data PC : Set where
  waiting : PC
  selected : Types.TypedResult → PC
  responderTracing initiatorTracing : RunResult → PC
  deadReady deadTracing finished : Finish → PC
record State : Set where
  constructor monitorState
  field base : P.State
        pcs : Store WorkerId PC
open State public
initial : O.Configuration → Maybe State
initial c with P.initial c
... | nothing = nothing
... | just p = just (monitorState p [])
source : State → O.Configuration
source s = P.source (base s)
setSource : O.Configuration → State → State
setSource c s = record s { base = P.setSource c (base s) }
poolAt : WorkerId → State → Pool.State
poolAt w s = P.poolAt w (base s)
setPool : WorkerId → U.Frame → Pool.State → State → State
setPool w f p s = record s { base = P.setPool w f p (base s) }
pcAt : WorkerId → State → PC
pcAt w s with lookup w (pcs s)
... | nothing = waiting
... | just pc = pc
setPC : WorkerId → PC → State → State
setPC w pc s = record s { pcs = put w pc (pcs s) }
ownerContext : WorkerId → State → Maybe (U.Frame × MuxId)
ownerContext w s with lookup w (U.frames (P.base (base s)))
... | nothing = nothing
... | just f with U.progress f | P.monitoring f
...   | U.promisePublished hid mid | true = just (f , mid)
...   | _ | _ = nothing
muxAt : MuxId → State → Maybe Mux.Mux
muxAt mid s = P.muxAt mid (base s)
viaSource : IG.IGAction → State → Maybe State
viaSource action s with O.advance (O.inbound (M.igStep action)) (source s)
... | nothing = nothing
... | just c = just (setSource c s)

-- Only this monitor's own continuation is suspended. Child publication,
-- insertion/removal and unrelated actors may proceed while a result is held.
localWaiting : WorkerId → State → Bool
localWaiting w s with pcAt w s
... | waiting = true
... | _ = false
delegateAllowed : P.Action → State → Bool
delegateAllowed (P.control w _) s = localWaiting w s
delegateAllowed (P.forkResponder w _ _) s = localWaiting w s
delegateAllowed (P.forkInitiator w _ _ _) s = localWaiting w s
delegateAllowed _ s = true
inherit : P.Action → State → Maybe State
inherit action s with delegateAllowed action s
... | false = nothing
... | true with P.step action (base s)
...   | nothing = nothing
...   | just next = just (record s { base = next })

-- Capture the authoritative typed HEAD once. The responder-only legacy queue
-- is untouched until the matching responder result is handled below.
selectHead : WorkerId → State → Maybe State
selectHead w s with pcAt w s | ownerContext w s
... | waiting | just (f , mid) with muxAt mid s | P.noParent (poolAt w s) | Pool.completions (poolAt w s)
...   | just m | true | item ∷ rest with Mux.status m | Mux.callback m
...     | Mux.ready | Mux.returned with Pool.step Pool.consumeCompletion (poolAt w s)
...       | nothing = nothing
...       | just next = just (setPC w (selected item) (setPool w f next s))
selectHead w s | waiting | just (f , mid) | just m | true | item ∷ rest | _ | _ = nothing
selectHead w s | waiting | just (f , mid) | _ | _ | _ = nothing
selectHead w s | _ | _ = nothing

-- Generation identity and captured outcome must match the selected physical
-- result. No current protocol-number slot or CM binding is used as identity.
findCaptured : WorkerId → Mux.JobDirection → ℕ → RunId → RunResult →
  Store JobId Types.ProtocolJob → Maybe (JobId × Types.ProtocolJob)
findCaptured w dir n gen outcome [] = nothing
findCaptured w dir n gen outcome ((j , job) ∷ rest) with
  does (w ≟ Types.owner job) ∧ P.sameDirection dir (Types.direction job) ∧
  does (n Nat.≟ Types.protocolNumber job) ∧ does (gen ≟ Types.generation job)
... | false = findCaptured w dir n gen outcome rest
... | true with Types.phase job
...   | Types.resultCaptured actual with P.sameOutcome outcome actual
...     | true = just (j , job)
...     | false = nothing
findCaptured w dir n gen outcome ((j , job) ∷ rest) | true | _ = nothing
legacyMatches : ℕ → RunResult → List Mux.JobResult → Bool
legacyMatches n outcome (Mux.jobResult Mux.responderJob actual result ∷ rest) =
  does (n Nat.≟ actual) ∧ P.sameOutcome outcome result
legacyMatches _ _ _ = false

-- Match the responder projection only for a responder typed head. Initiator
-- traces are ignored by the IG tracer; their local finish input observes that
-- separate trace/DeltaQ return without writing an old PeerActions cell.
protocolSource : WorkerId → MuxId → Mux.JobDirection → ℕ → RunResult → State → Maybe State
protocolSource w mid Mux.responderJob n outcome s with muxAt mid s
... | nothing = nothing
... | just m with legacyMatches n outcome (Mux.completions m)
...   | false = nothing
...   | true with viaSource (IG.monitorCompletion mid) s
...     | nothing = nothing
...     | just next = just (setPC w (responderTracing outcome) next)
protocolSource w mid Mux.initiatorJob n clean s = just (setPC w (initiatorTracing clean) s)
protocolSource w mid Mux.initiatorJob n (errored err) s with viaSource (IG.recordMuxFailure mid err) s
... | nothing = nothing
... | just next = just (setPC w (initiatorTracing (errored err)) next)
handleProtocol : WorkerId → Mux.JobDirection → ℕ → RunId → RunResult → State → Maybe State
handleProtocol w dir n gen outcome s with ownerContext w s |
  findCaptured w dir n gen outcome (P.jobs (base s))
... | just (f , mid) | just (j , job) with does (Types.mux job ≟ mid) | muxAt mid s
...   | true | just m with Mux.status m | Mux.callback m
...     | Mux.ready | Mux.returned = protocolSource w mid dir n outcome s
...     | _ | _ = nothing
handleProtocol w dir n gen outcome s | just (f , mid) | just (j , job) | _ | _ = nothing
handleProtocol w dir n gen outcome s | _ | _ = nothing

-- Source readGroupSize counts CURRENT registered MiniProtocolJob handles,
-- including returned/published jobs awaiting removal, excluding engine jobs and
-- removed history. The count is recomputed at handling, not cached at dequeue.
countMini : WorkerId → List JobId → Store JobId Types.ProtocolJob → ℕ
countMini w [] jobs = zero
countMini w (j ∷ rest) jobs with lookup j jobs
... | nothing = countMini w rest jobs
... | just job with does (w ≟ Types.owner job)
...   | true = suc (countMini w rest jobs)
...   | false = countMini w rest jobs
miniCount : WorkerId → State → ℕ
miniCount w s = countMini w (Pool.registered (poolAt w s)) (P.jobs (base s))
demuxFinish : WorkerId → ErrorId → State → Finish
demuxFinish w err s with isBearerClosed err ∧ does (miniCount w s Nat.≟ zero)
... | true = normal
... | false = failed err
statusAction : Finish → MuxId → IG.IGAction
statusAction normal mid = IG.recordMuxStopped mid
statusAction (failed err) mid = IG.recordMuxFailure mid err
recordFinish : WorkerId → Finish → State → Maybe State
recordFinish w outcome s with ownerContext w s
... | nothing = nothing
... | just (f , mid) with viaSource (statusAction outcome mid) s
...   | nothing = nothing
...   | just next = just (setPC w (deadReady outcome) next)
handleHead : WorkerId → State → Maybe State
handleHead w s with pcAt w s
... | selected (Types.protocolCompletion dir n gen outcome) = handleProtocol w dir n gen outcome s
... | selected (Types.infraMuxer err) = recordFinish w (failed err) s
... | selected (Types.infraDemuxer err) = recordFinish w (demuxFinish w err s) s
... | _ = nothing

tracing : PC → Bool
tracing (responderTracing _) = true
tracing (deadTracing _) = true
tracing _ = false
traceSource : Bool → WorkerId → State → Maybe State
traceSource sample w s with tracing (pcAt w s) | ownerContext w s
... | true | just (f , mid) with sample
...   | true = viaSource (IG.sampleTracer mid) s
...   | false = viaSource (IG.commitTracer mid) s
traceSource sample w s | _ | _ = nothing

-- A completion trace must return before another physical result can be selected.
-- A responder error's afterFailure continuation separately begins the Dead trace.
finishProtocol : WorkerId → State → Maybe State
finishProtocol w s with pcAt w s | ownerContext w s
... | responderTracing clean | just (f , mid) with muxAt mid s
...   | just m with Mux.callback m
...     | Mux.returned = just (setPC w waiting s)
...     | _ = nothing
finishProtocol w s | responderTracing clean | just (f , mid) | nothing = nothing
finishProtocol w s | responderTracing (errored err) | just (f , mid) with muxAt mid s
... | just m with Mux.callback m
...   | Mux.afterFailure = just (setPC w (deadReady (failed err)) s)
...   | _ = nothing
finishProtocol w s | responderTracing (errored err) | just (f , mid) | nothing = nothing
finishProtocol w s | initiatorTracing outcome | just (f , mid) with muxAt mid s
... | just m with Mux.callback m
...   | Mux.returned = just (setPC w (next outcome) s)
  where
  next : RunResult → PC
  next clean = waiting
  next (errored err) = deadReady (failed err)
...   | _ = nothing
finishProtocol w s | initiatorTracing outcome | just (f , mid) | nothing = nothing
finishProtocol w s | _ | _ = nothing

-- Local event matching keeps the terminal outcome equal to the actual status.
finishMatches : Finish → Mux.Status → Bool
finishMatches normal Mux.stopped = true
finishMatches (failed err) (Mux.failed actual) = does (ErrorId.errorNumber err Nat.≟ ErrorId.errorNumber actual)
finishMatches _ _ = false
deadAction : Finish → Mux.Callback → MuxId → Maybe IG.IGAction
deadAction (failed _) Mux.afterFailure mid = just (IG.monitorCommand mid)
deadAction outcome Mux.returned mid = just (IG.traceMuxDead mid)
deadAction _ _ _ = nothing
startDead : WorkerId → State → Maybe State
startDead w s with pcAt w s | ownerContext w s
... | deadReady outcome | just (f , mid) with muxAt mid s
...   | just m with finishMatches outcome (Mux.status m) | deadAction outcome (Mux.callback m) mid
...     | true | just action with viaSource action s
...       | nothing = nothing
...       | just next = just (setPC w (deadTracing outcome) next)
startDead w s | deadReady outcome | just (f , mid) | just m | _ | _ = nothing
startDead w s | deadReady outcome | just (f , mid) | nothing = nothing
startDead w s | _ | _ = nothing
finishMux : WorkerId → State → Maybe State
finishMux w s with pcAt w s | ownerContext w s
... | deadTracing outcome | just (f , mid) with muxAt mid s
...   | just m with Mux.callback m | finishMatches outcome (Mux.status m)
...     | Mux.returned | true = just (setPC w (finished outcome) s)
...     | _ | _ = nothing
finishMux w s | deadTracing outcome | just (f , mid) | nothing = nothing
finishMux w s | _ | _ = nothing

data Action : Set where
  run : P.Action → Action
  consume handleSelected sampleTracer commitTracer finishProtocolTrace beginDead finishDead : WorkerId → Action
step : Action → State → Maybe State
step (run action) s = inherit action s
step (consume w) s = selectHead w s
step (handleSelected w) s = handleHead w s
step (sampleTracer w) s = traceSource true w s
step (commitTracer w) s = traceSource false w s
step (finishProtocolTrace w) s = finishProtocol w s
step (beginDead w) s = startDead w s
step (finishDead w) s = finishMux w s

-- Finished describes only this monitor continuation. Outstanding jobs, queue
-- tails, whole-pool joins, buffer release and handler Async results remain for
-- future integration; unrelated actors are never globally frozen here.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
