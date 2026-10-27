{-# OPTIONS --guardedness #-}

-- Conditional registered snapshots for the A3 commitTracer integration.
-- These equations describe actual stepWorker outcomes after prefixReady is
-- wired before missingDescriptor. They are not source-reachability claims.
module ConnectionManagement.Negative.TracerReadinessIntegration where

open import Data.Bool using (true)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InformationChannel as Channel
import ConnectionManagement.CSP.IGRegistration as Fixture
open import ConnectionManagement.Scenarios.Admission using (key₀)

-- The registration has hot protocol 1, so traced protocol 99 is absent. Its
-- RemoteIdle timer is ident 1; changing readiness does not replace descriptors.
base expiredBase : IG.Runtime
base = I.inboundGovernor Fixture.registered
expiredBase = record base { execution = record (IG.execution base)
  { timers = (ident 0 , ticking) ∷ (ident 1 , expired) ∷ [] } }
zeroCounters nonzeroCounters : M.Counters
zeroCounters = M.counters (+ 0) (+ 0)
nonzeroCounters = M.counters (+ 1) (+ 0)
fullQueue almostFullQueue : List IGEvent
fullQueue = replicate Channel.capacity (muxFinished key₀)
almostFullQueue = replicate 99 (muxFinished key₀)

-- Keep the source callback and its counters explicit in every input/output.
callback : M.Trace → M.Counters → IG.Runtime → IG.Runtime
callback tr rc r = IG.setMux Fixture.mid (record Fixture.armedMux
  { traceCounters = just rc; callback = M.commitTrace true tr }) r
fault : M.Counters → IG.Runtime → IG.Runtime
fault rc r = IG.setMux Fixture.mid (record Fixture.armedMux
  { traceCounters = just rc; callback = M.tracerFailed 99 }) r

-- Expired RemoteIdle wins over a missing start descriptor, without a successor
-- that partially publishes AwakeRemote or changes a counter.
expired-start-retries : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.started 99) zeroCounters expiredBase) [] ≡ nothing
expired-start-retries = refl
expired-full-start-retries : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.started 99) zeroCounters expiredBase) fullQueue ≡ nothing
expired-full-start-retries = refl

-- With an unexpired timer, the initial AwakeRemote write can retry first.
full-start-retries : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.started 99) zeroCounters base) fullQueue ≡ nothing
full-start-retries = refl

-- Empty/one-slot queues reach the descriptor fault. Even the successful prefix
-- probe is not committed: the output queue and counters remain unchanged.
drained-start-faults : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.started 99) zeroCounters base) [] ≡ just (fault zeroCounters base , [])
drained-start-faults = refl
one-slot-start-faults : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.started 99) zeroCounters base) almostFullQueue ≡
  just (fault zeroCounters base , almostFullQueue)
one-slot-start-faults = refl

-- Nonzero counters omit the AwakeRemote prefix, so queue fullness does not
-- shield the missing-descriptor exception.
nonzero-full-start-faults : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.started 99) nonzeroCounters base) fullQueue ≡
  just (fault nonzeroCounters base , fullQueue)
nonzero-full-start-faults = refl

-- Completion payloads are strict in the source. Their descriptor faults occur
-- before capacity retry and do not use the start-only RemoteIdle expiry gate.
expired-full-clean-completion-faults : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.completed 99 clean) zeroCounters expiredBase) fullQueue ≡
  just (fault zeroCounters expiredBase , fullQueue)
expired-full-clean-completion-faults = refl
full-error-completion-faults : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.completed 99 (errored (errorId 0))) zeroCounters base) fullQueue ≡
  just (fault zeroCounters base , fullQueue)
full-error-completion-faults = refl

-- A known hot start still needs the whole two-message burst and counter write.
-- Prefix readiness with one slot does not permit a partial AwakeRemote commit.
known-start-whole-burst-retries : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.started 1) zeroCounters base) almostFullQueue ≡ nothing
known-start-whole-burst-retries = refl
known-start-commits : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.started 1) zeroCounters base) [] ≡ just
  (IG.setMux Fixture.mid (record Fixture.armedMux
    { traceCounters = just nonzeroCounters; callback = M.afterStart 1 }) base ,
   awakeRemote key₀ ∷ remotePromotedToHot key₀ ∷ [])
known-start-commits = refl

-- Idle expiry alone does not block a known completed callback. Queue and
-- last-hot counter effects still commit as a single three-message transaction.
known-expired-completion-commits : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.completed 1 clean) nonzeroCounters expiredBase) [] ≡ just
  (IG.setMux Fixture.mid (record Fixture.armedMux
    { traceCounters = just zeroCounters; callback = M.returned }) expiredBase ,
   miniProtocolTerminated (terminatedProtocol key₀ Fixture.mid Fixture.proto duplex clean) ∷
   remoteDemotedToWarm key₀ ∷ waitIdleRemote key₀ ∷ [])
known-expired-completion-commits = refl
known-expired-full-completion-retries : IG.stepWorker (IG.commitTracer Fixture.mid)
  (callback (M.completed 1 clean) nonzeroCounters expiredBase) fullQueue ≡ nothing
known-expired-full-completion-retries = refl
