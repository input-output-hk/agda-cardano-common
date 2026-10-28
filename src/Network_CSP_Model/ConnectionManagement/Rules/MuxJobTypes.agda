{-# OPTIONS --guardedness #-}

-- Physical queued mux-job payloads, distinguished from the legacy responder
-- projection and from mutable current mini-protocol status/result cells.
module ConnectionManagement.Rules.MuxJobTypes where

open import Data.Nat using (ℕ)
open import ConnectionManagement.Domain hiding (mux)
open import ConnectionManagement.IGTypes using (RunResult)
import ConnectionManagement.Rules.MuxRuntime as M

data Role : Set where
  muxer demuxer : Role
data TypedResult : Set where
  infraMuxer infraDemuxer : ErrorId → TypedResult
  protocolCompletion : M.JobDirection → ℕ → RunId → RunResult → TypedResult

data BodyPhase : Set where
  executing waitingEgress : BodyPhase
  resultCaptured : RunResult → BodyPhase
record ProtocolJob : Set where
  constructor protocolJob
  field owner : WorkerId
        mux : MuxId
        direction : M.JobDirection
        protocolNumber : ℕ
        generation : RunId
        phase : BodyPhase
open ProtocolJob public

infraResult : Role → ErrorId → TypedResult
infraResult muxer err = infraMuxer err
infraResult demuxer err = infraDemuxer err
