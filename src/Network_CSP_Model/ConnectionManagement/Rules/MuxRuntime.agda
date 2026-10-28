{-# OPTIONS --guardedness #-}

-- Source runMiniProtocolSTM (Mux.hs:749-789) and IG tracer (IG:635-728).
-- Scheduling/traffic/termination inputs are explicit runtime boundaries.
module ConnectionManagement.Rules.MuxRuntime where

open import Class.DecEq.Instances using (DecEq-ℕ)
open import Data.Nat using (ℕ; zero; _≟_)
open import Data.Integer using (ℤ; +_)
import Data.Integer as Z
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Rules.InformationChannel as Channel

-- Ready remains the mux status while the monitor runs.
data Status : Set where
  ready stopping stopped : Status
  failed : ErrorId → Status

data ProtocolStatus : Set where
  idle demand demandAny running : ProtocolStatus

data Command : Set where
  startCommand : Protocol → Command
  shutdown : Command

-- Source fields are signed Ints. Unbounded integers preserve negative values;
-- machine-word overflow is outside this small-counter execution profile.
record Counters : Set where
  constructor counters
  field hotCount nonHotCount : ℤ
open Counters public

data Trace : Set where
  started : ℕ → Trace
  completed : ℕ → RunResult → Trace
  muxStopped : Trace

-- activeVar is read before, and independently of, the tracer STM transaction.
data Callback : Set where
  readActive : Trace → Callback
  commitTrace : Bool → Trace → Callback
  afterStart forkPending : ℕ → Callback
  afterFailure : Callback
  tracerFailed : ℕ → Callback
  returned : Callback

-- Explicit async observation points in the unmasked tracer/callback body.
-- afterStart/afterFailure retain already committed STM effects; forkPending is
-- outside this profile because fork/registration has its own masking contract.
interruptibleCallback : Callback → Bool
interruptibleCallback (readActive _) = true
interruptibleCallback (commitTrace _ _) = true
interruptibleCallback (afterStart _) = true
interruptibleCallback afterFailure = true
interruptibleCallback _ = false

-- Both directions publish job results into the same source JobPool FIFO.
-- Direction separates initiator/responder jobs with the same protocol number.
data JobDirection : Set where
  initiatorJob responderJob : JobDirection
record JobResult : Set where
  constructor jobResult
  field jobDirection : JobDirection
        jobNumber : ℕ
        jobOutcome : RunResult
open JobResult public

-- Tracer attachment belongs to the mux; cleared counters do not detach it.
data TracerAttachment : Set where
  noIGTracer igTracer : TracerAttachment

record Mux : Set where
  constructor muxState
  field
    key : ConnectionKey
    status : Status
    protocols : Store ℕ ProtocolStatus
    commands : List Command
    waiting : Store ℕ StartMode
    runningJobs : List ℕ
    finishedJobs : List (ℕ × RunResult)
    completions : List JobResult
    traceCounters : Maybe Counters
    callback : Callback
    tracerAttachment : TracerAttachment
open Mux public

record Handle : Set where
  constructor handleState
  field muxRef : MuxId
        bundle : List Protocol
        versionFlow : DataFlow
open Handle public

data StartError : Set where
  unknownProtocol alreadyRunning shutdownError : StartError

-- A caught exception rolls back the failing runMiniProtocolSTM invocation,
-- but not earlier successful invocations in the enclosing foldM transaction.
data StartResult : Set where
  startedAll : Mux → StartResult
  startFailed : ℕ → StartError → Mux → StartResult

startStatus : StartMode → ProtocolStatus
startStatus onDemand = demand
startStatus onDemandAny = demandAny
startStatus eagerly = running

startOne : Protocol → Mux → StartResult
startOne p m with lookup (number p) (protocols m)
... | nothing = startFailed (number p) unknownProtocol m
... | just st with status m
...   | stopping = startFailed (number p) shutdownError m
...   | stopped = startFailed (number p) shutdownError m
...   | failed _ = startFailed (number p) shutdownError m
...   | ready with st
...     | idle = startedAll (record m
          { protocols = put (number p) (startStatus (startMode p)) (protocols m)
          ; commands = commands m ++ (startCommand p ∷ []) })
...     | _ = startFailed (number p) alreadyRunning m

startBundle : List Protocol → Mux → StartResult
startBundle [] m = startedAll m
startBundle (p ∷ ps) m with startOne p m
... | startFailed n err updated = startFailed n err updated
... | startedAll updated = startBundle ps updated

-- The current registration supplies the temperature/descriptor and captured mux;
-- the counters belong to the callback's originating mux, even after key reuse.
record View : Set where
  constructor view
  field captured : MuxId
        registeredBundle : List Protocol
        flow : DataFlow
        idleExpired : Bool
open View public

findProtocol : ℕ → List Protocol → Maybe Protocol
findProtocol n [] = nothing
findProtocol n (p ∷ ps) with n ≟ number p
... | yes _ = just p
... | no _ = findProtocol n ps

startEvents : ConnectionKey → Temperature → Counters → List IGEvent
startEvents k hot (counters (+ zero) (+ zero)) = awakeRemote k ∷ remotePromotedToHot k ∷ []
startEvents k hot (counters (+ zero) c) = remotePromotedToHot k ∷ []
startEvents k hot _ = []
startEvents k _ (counters (+ zero) (+ zero)) = awakeRemote k ∷ []
startEvents k _ _ = []

increase decrease : Temperature → Counters → Counters
increase hot (counters h c) = counters (Z.suc h) c
increase _ (counters h c) = counters h (Z.suc c)
decrease hot (counters h c) = counters (Z.pred h) c
decrease _ (counters h c) = counters h (Z.pred c)

demoteEvents : ConnectionKey → Temperature → ℤ → List IGEvent
demoteEvents k hot (+ 1) = remoteDemotedToWarm k ∷ []
demoteEvents k _ _ = []
idleEvents : ConnectionKey → ℤ → List IGEvent
idleEvents k (+ 1) = waitIdleRemote k ∷ []
idleEvents k _ = []
endEvents : ConnectionKey → Protocol → RunResult → View → Counters → List IGEvent
endEvents k p (errored err) v rc = miniProtocolTerminated
  (terminatedProtocol k (captured v) p (flow v) (errored err)) ∷ []
endEvents k p clean v rc = miniProtocolTerminated
  (terminatedProtocol k (captured v) p (flow v) clean) ∷
  (demoteEvents k (temperature p) (hotCount rc) ++ idleEvents k (hotCount rc Z.+ nonHotCount rc))

-- nothing is retry (or an invalid missing protocol descriptor). Queue and
-- counters are returned together so no partial burst/counter commit is visible.
traceSTM : ConnectionKey → Trace → Maybe View → Maybe Counters → List IGEvent →
  Maybe (Maybe Counters × List IGEvent)
traceSTM k muxStopped v rc queue with Channel.writeMessage (muxFinished k) queue
... | nothing = nothing
... | just q = just (nothing , q)
traceSTM k (started n) nothing rc queue = just (nothing , queue)
traceSTM k (started n) (just v) nothing queue = just (nothing , queue)
traceSTM k (started n) (just v) (just rc) queue with findProtocol n (registeredBundle v)
... | nothing = nothing
... | just p with idleExpired v
...   | true = nothing
...   | false with Channel.writeBurst (startEvents k (temperature p) rc) queue
...     | nothing = nothing
...     | just q = just (just (increase (temperature p) rc) , q)
traceSTM k (completed n result) nothing rc queue = just (nothing , queue)
traceSTM k (completed n result) (just v) nothing queue = just (nothing , queue)
traceSTM k (completed n result) (just v) (just rc) queue with findProtocol n (registeredBundle v)
... | nothing = nothing
... | just p with Channel.writeBurst (endEvents k p result v rc) queue
...   | nothing = nothing
...   | just q with result
...     | clean = just (just (decrease (temperature p) rc) , q)
...     | errored _ = just (nothing , q)
