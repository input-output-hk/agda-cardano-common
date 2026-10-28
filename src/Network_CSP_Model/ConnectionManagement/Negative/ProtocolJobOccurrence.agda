{-# OPTIONS --guardedness #-}

-- Conditional pending-result fixtures: duplicate protocol numbers name distinct
-- runs. These test occurrence selection, not source reachability of the snapshot.
module ConnectionManagement.Negative.ProtocolJobOccurrence where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (responderMode; noResponderMode; clean; errored)
open import ConnectionManagement.Store using (put)
open import ConnectionManagement.Scenarios.Admission using (key₀)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M

mid : MuxId
mid = ident 0
newerError : ErrorId
newerError = errorId 9
pending : M.Mux
pending = M.muxState key₀ M.ready [] [] [] []
  ((1 , clean) ∷ (1 , errored newerError) ∷ []) [] nothing M.returned M.noIGTracer
fixture : IG.Runtime
fixture = IG.setMux mid pending IG.initial
newerFirst : IG.Runtime
newerFirst = IG.setMux mid (record pending
  { finishedJobs = (1 , clean) ∷ []
  ; completions = M.jobResult M.responderJob 1 (errored newerError) ∷ [] }) fixture
olderFirst : IG.Runtime
olderFirst = IG.setMux mid (record pending
  { finishedJobs = (1 , errored newerError) ∷ []
  ; completions = M.jobResult M.responderJob 1 clean ∷ [] }) fixture

newer-same-number-overtakes : IG.step responderMode
  (IG.publishJobOccurrence mid 1) fixture [] ≡ just (newerFirst , [])
newer-same-number-overtakes = refl
older-occurrence-remains : IG.takePending 0 (M.finishedJobs pending) ≡
  just ((1 , clean) , (1 , errored newerError) ∷ [])
older-occurrence-remains = refl
legacy-still-selects-first : IG.step responderMode
  (IG.publishJobResult mid 1) fixture [] ≡ just (olderFirst , [])
legacy-still-selects-first = refl
out-of-range-refused : IG.step responderMode
  (IG.publishJobOccurrence mid 2) fixture [] ≡ nothing
out-of-range-refused = refl
initiator-only-refused : IG.step noResponderMode
  (IG.publishJobOccurrence mid 1) fixture [] ≡ nothing
initiator-only-refused = refl
