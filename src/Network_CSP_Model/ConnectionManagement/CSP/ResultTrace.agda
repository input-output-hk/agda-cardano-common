{-# OPTIONS --guardedness #-}

-- Lossless diagnostic trace object. Labels retain both states, so all API,
-- protocol, physical async and STM results remain observable without inventing
-- a second transition relation. This is not an API-only hiding policy.
open import Data.Maybe using (Maybe)
module ConnectionManagement.CSP.ResultTrace
  (State Action : Set) (advance : Action → State → Maybe State) where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
import ConnectionManagement.CSP.Dispatcher as Dispatcher
module Raw = Dispatcher State Action advance
open import Process_Trees using (ExtI)
open import Semantics.Failures {E = Raw.Channel} {I = ExtI Raw.Channel} using (traces)

-- A full state snapshot is intentional: action-only return labels omit values.
record Observation : Set where
  constructor observation
  field before : State
        action : Action
        after : State
open Observation public

-- The trace renderer uses exactly the existing successful dispatcher edges.
data Recorded : State → List Observation → State → Set where
  stop : ∀ {s} → Recorded s [] s
  more : ∀ {s a t os u} → advance a s ≡ just t → Recorded t os u →
    Recorded s (observation s a t ∷ os) u

record-run : ∀ {s as t} → Raw.Executes s as t →
  Σ (List Observation) (λ os → map action os ≡ as × Recorded s os t)
record-run Raw.done = [] , refl , stop
record-run (Raw.next {s = s} {t = t} {a = a} eq rest) with record-run rest
... | os , refl , recorded = observation s a t ∷ os , refl , more eq recorded

erase : ∀ {s os t} → Recorded s os t → Raw.Executes s (map action os) t
erase stop = Raw.done
erase (more eq rest) = Raw.next eq (erase rest)

-- Every value-complete trace is a PTree trace after erasing snapshots.
recorded-trace : ∀ {s os t} → Recorded s os t →
  traces (Raw.Process s) (map Raw.label (map action os))
recorded-trace recorded = Raw.trace-intro (erase recorded)

-- Conversely every raw PTree trace has a lossless observation completion.
all-trace-recorded : ∀ {s es} → traces (Raw.Process s) es →
  Σ (List Observation) (λ os → Σ State (λ t →
    es ≡ map Raw.label (map action os) × Recorded s os t))
all-trace-recorded (_ , tr) with Raw.all-exec-inv tr
... | as , t , refl , endpoint , run with record-run run
...   | os , refl , recorded = os , t , refl , recorded

-- Any result query on either snapshot separates unequal returned values.
-- No equality decision or serialization of the entire runtime is assumed.
result-distinguishes : ∀ {Value : Set} (query : State → Value) {x y} →
  query (after x) ≢ query (after y) → x ≢ y
result-distinguishes query different refl = different refl
input-distinguishes : ∀ {Value : Set} (query : State → Value) {x y} →
  query (before x) ≢ query (before y) → x ≢ y
input-distinguishes query different refl = different refl

-- With a fixed initial state, erasure loses no result information: deterministic
-- dispatch reconstructs a unique snapshot sequence from the complete actions.
open import Data.Maybe.Properties using (just-injective)
open import Data.List.Properties using (∷-injective)
open import Relation.Binary.PropositionalEquality using (sym; trans)
recorded-deterministic : ∀ {s os ps t u} → Recorded s os t → Recorded s ps u →
  map action os ≡ map action ps → os ≡ ps
recorded-deterministic stop stop refl = refl
recorded-deterministic stop (more eq rest) ()
recorded-deterministic (more eq rest) stop ()
recorded-deterministic (more left xs) (more right ys) same with ∷-injective same
... | refl , tail with just-injective (trans (sym left) right)
...   | refl rewrite recorded-deterministic xs ys tail = refl
