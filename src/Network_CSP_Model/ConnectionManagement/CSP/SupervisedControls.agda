{-# OPTIONS --guardedness #-}

-- Current-runtime controls: observation separation, relays gate, and distinct
-- input/fuel/refusal replay frontiers. The old counterexamples are unchanged.
module ConnectionManagement.CSP.SupervisedControls where

open import Data.Bool using (true)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import ConnectionManagement.CSP.SupervisedWitness as Witness
import ConnectionManagement.Negative.InboundCleanLifecycle as Run
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.PoolRelays as Pool
module B = Witness.B
module O = B.O
module R = Witness.Replay
module Values = Witness.Values
module W = Witness.W

-- Domain frontiers retain the distinction between failure to dispatch an
-- actual typed event and a declared input-adapter/model coverage boundary.
data Frontier : Set where
  complete cutoff malformed-input incomplete-model disabled-event : Frontier
frontier : ∀ {s rs} → R.Report s rs → Frontier
frontier R.complete = complete
frontier R.cutoff = cutoff
frontier R.malformed-input = malformed-input
frontier R.model-frontier = incomplete-model
frontier (R.refused eq) = disabled-event
frontier (R.advanced eq tail) = frontier tail

cancel : O.OuterAction
cancel = O.relaysAct Pool.requestCancel
cancel-before-return : O.outerStep cancel Witness.start ≡ nothing
cancel-before-return = refl
cutoff-control : frontier (R.replay 0 Witness.start (R.event cancel ∷ [])) ≡ cutoff
cutoff-control = refl
refusal-control : frontier (R.replay 1 Witness.start (R.event cancel ∷ [])) ≡ disabled-event
refusal-control = refl
malformed-control : frontier (R.replay 1 Witness.start (R.malformed 0 ∷ [])) ≡ malformed-input
malformed-control = refl
missing-model-control : frontier (R.replay 1 Witness.start (R.unsupported 0 ∷ [])) ≡ incomplete-model
missing-model-control = refl
empty-is-complete : frontier (R.replay 0 Witness.start []) ≡ complete
empty-is-complete = refl

-- A repeated event label does not merge unequal result-bearing observations.
-- This tests the lossless alphabet itself, not reachability of forged labels.
query : O.Outer → Maybe W.BodyResult
query s = W.resultOf A.child₀ (Run.handlerState (O.inner s))
before-result after-result : Values.Observation
before-result = Values.observation Witness.start cancel (O.outer Run.s17 (Pool.initial true))
after-result = Values.observation Witness.start cancel Witness.end
same-action : Values.action before-result ≡ Values.action after-result
same-action = refl
different-values : query (Values.after before-result) ≢ query (Values.after after-result)
different-values ()
observations-distinct : before-result ≢ after-result
observations-distinct = Values.result-distinguishes query different-values

-- One source-backed ordinary wait explanation: the outer cancellation must
-- wait for the inner Server callback to return. Other disabled events remain
-- unclassified unless a caller supplies a similarly explicit contract.
open import Data.Bool using (false)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
Blocking : O.Outer → O.OuterAction → Set
Blocking s a = a ≡ cancel × O.runtimeReturned (O.inner s) ≡ false
Missing : O.Outer → O.OuterAction → Set
Missing s a = ⊥
module Explanation = R.Explain Blocking Missing
cancel-explanation : Explanation.Refusal Witness.start cancel
cancel-explanation = Explanation.explanation cancel-before-return
  (Explanation.ordinary-blocking (refl , refl))
