{-# OPTIONS --guardedness #-}

-- Physical queued mux-job payloads, distinguished from the legacy responder
-- projection and from mutable current mini-protocol status/result cells.
module ConnectionManagement.Rules.MuxJobTypes where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl; cong)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain hiding (mux)
open import ConnectionManagement.IGTypes using (RunResult)
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.MuxEgress as E

data Role : Set where
  muxer demuxer : Role
  laneMuxer : E.Lane → Role
instance
  DecEq-Role : DecEq Role
  DecEq-Role ._≟_ muxer muxer = yes refl
  DecEq-Role ._≟_ muxer demuxer = no (λ ())
  DecEq-Role ._≟_ muxer (laneMuxer _) = no (λ ())
  DecEq-Role ._≟_ demuxer muxer = no (λ ())
  DecEq-Role ._≟_ demuxer demuxer = yes refl
  DecEq-Role ._≟_ demuxer (laneMuxer _) = no (λ ())
  DecEq-Role ._≟_ (laneMuxer _) muxer = no (λ ())
  DecEq-Role ._≟_ (laneMuxer _) demuxer = no (λ ())
  DecEq-Role ._≟_ (laneMuxer l) (laneMuxer r) with l ≟ r
  ... | yes refl = yes refl
  ... | no apart = no (λ { refl → apart refl })

-- A source plan has one legacy plain muxer or the actual ordered lane muxers,
-- followed by the one demuxer; result tags do not encode the lane.
infraPlan : E.Layout → List Role
infraPlan E.plainLayout = muxer ∷ demuxer ∷ []
infraPlan (E.scheduledLayout false) = laneMuxer E.directLane ∷ laneMuxer E.scheduledLane ∷ demuxer ∷ []
infraPlan (E.scheduledLayout true) = laneMuxer E.directLane ∷ laneMuxer E.scheduledLane ∷ laneMuxer E.sliceLane ∷ demuxer ∷ []
roleForLane : E.Layout → E.Lane → Maybe Role
roleForLane E.plainLayout E.scheduledLane = just muxer
roleForLane E.plainLayout _ = nothing
roleForLane (E.scheduledLayout _) E.directLane = just (laneMuxer E.directLane)
roleForLane (E.scheduledLayout _) E.scheduledLane = just (laneMuxer E.scheduledLane)
roleForLane (E.scheduledLayout true) E.sliceLane = just (laneMuxer E.sliceLane)
roleForLane (E.scheduledLayout false) E.sliceLane = nothing
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
infraResult (laneMuxer _) err = infraMuxer err
