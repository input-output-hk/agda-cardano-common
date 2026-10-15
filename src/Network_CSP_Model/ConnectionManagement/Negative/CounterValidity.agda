{-# OPTIONS --guardedness #-}

-- Malformed-state negative controls, not source-reachable counterexamples.
module ConnectionManagement.Negative.CounterValidity where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Counters
open import ConnectionManagement.Properties.CounterState
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Fixtures
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀; key₀; remoteAddr; localAddr)
import ConnectionManagement.Rules.Server as Server

-- Check actual snapshots without normalizing an entire machine execution.
start-valid : CounterStateValid (world start)
start-valid = [] ∷ []

waiting-valid : CounterStateValid (world waiting)
waiting-valid = count-valid _ _ {n = 1} refl ∷ []

committed-valid : CounterStateValid (world committed)
committed-valid = count-valid _ _ {n = 1} refl ∷ []

cleaned-valid : ∀ pc → admissionMaps pc ≡ [] → CounterStateValid (world (cleaned pc))
cleaned-valid pc eq rewrite eq = [] ∷ []

-- A cleanup modifier retains its saved and proposed maps, even though the
-- global cell is empty. Both are checked against the current heap.
locked : Configuration
locked = snapshot unneg (taken child₀) (awaitHandshake promise₀ entry₀)
  (handling child₀) [] [] (cleanupStore (cleanupClose childLease [] countImmediately))

locked-valid : CounterStateValid (world locked)
locked-valid = count-valid _ _ {n = 1} refl ∷ [] ∷ []

-- Updating an entry does not invalidate the retained binding.
updated-binding-valid : CounterReferences ((entry₀ , terminated nothing) ∷ []) binding
updated-binding-valid = count-valid _ _ {n = 0} refl

-- Duplicate outer keys hide the second bucket from lookup, but traversal still
-- visits it. This is why lookup validity alone needs a uniqueness premise.
shadowed : ConnMap
shadowed = (remoteAddr , []) ∷
  (remoteAddr , (knownLocal localAddr , entry₀) ∷ []) ∷ []

shadowed-lookup-empty : lookupConnection key₀ shadowed ≡ nothing
shadowed-lookup-empty = refl

shadowed-count-fails : countIncoming [] shadowed ≡ nothing
shadowed-count-fails = refl

shadowed-invalid : ¬ CounterReferences [] shadowed
shadowed-invalid valid with count-total [] shadowed valid
... | n , ()

-- An ordinary full-map counter continuation can be disabled by bad references.
-- There is no lock contention here; this must not be reported as a source wedge.
malformed : Configuration
malformed = snapshot unneg (full shadowed) (countPublished promise₀ entry₀)
  (handling child₀) [] [] []

-- Use an empty heap, making the shadowed entry genuinely dangling.
bad : Configuration
bad = replaceWorld malformed (record (world malformed)
  { cm = cmStore (full shadowed) [] 0 })

bad-invalid : ¬ CounterStateValid (world bad)
bad-invalid (valid ∷ _) = shadowed-invalid valid

counterAttempt : Action
counterAttempt = admissionStep w₀ Server.readCounters

bad-counter-refused : advance counterAttempt bad ≡ nothing
bad-counter-refused = refl

open import Process_Trees using (ExtI)
open import Semantics.Refusals {E = Channel} {I = ExtI Channel} using (Refuses)

bad-csp-refusal : Refuses (Process bad) (λ e → e ≡ label counterAttempt)
bad-csp-refusal = singleton-refusal {c = bad} {a = counterAttempt} bad-counter-refused

-- A dangling saved map must also be rejected, despite the absent global value.
badSaved : State
badSaved = record (world locked) { cm = cmStore (taken child₀) [] 0 }

bad-saved-invalid : ¬ CounterStateValid badSaved
bad-saved-invalid ((((st , ()) ∷ _) ∷ _) ∷ _)
