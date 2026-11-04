{-# OPTIONS --guardedness #-}

-- Native/production instances and an environment-stuttering control delimit the step bound.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingNativeTests where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; replicate; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Unit using (⊤)
open import Data.Fin using () renaming (zero to fzero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Induction.WellFounded using (Acc)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeScheduling Notification as Policy
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification ⊤ as Cost
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤ as Native
import Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingBridge exactParams ⊤ as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownNativeTests as Fixture

-- Reuse the exact endpoints of the already inhabited production Done-before-Send race.
module Tree = Native.At S.nodeNext fzero fzero hi hi
-- One shared native specialization supplies accessibility and quantitative bounds.
module Proof = Bridge.At S.nodeNext fzero fzero hi hi
open Native using (module LTS; module Traces)

-- The production model has finite hidden paths even before forecast readiness.
initial-node-accessible : Acc (λ t s → Node.Tau s t) Node.initial
initial-node-accessible = Policy.tau-accessible Node.initial

-- An actual initial native process cannot have an infinite hidden path.
initial-no-divergence : ¬ LTS.Diverges (Tree.tree D.initial)
initial-no-divergence = Proof.no-hidden-divergence D.initial

-- The reachable remaining server Send-Done is one actual native wire operation.
last-hook : Tree.tree (Node.driverState Fixture.after-done)
  Traces.⟹∖√⟨ Tree.encode (D.serverSend D.done) ∷ [] ⟩ Tree.tree Fixture.closed
last-hook = Traces.∖√-ev Fixture.native-server-step Traces.∖√-refl

-- Divergence exclusion also applies to the actual target of that native continuation.
closed-no-divergence : ¬ LTS.Diverges (Tree.tree Fixture.closed)
closed-no-divergence = Proof.reachable-no-hidden-divergence last-hook

-- Both shutdown paths already hold at the actual source, so the native bound applies.
last-hook-bounded : Proof.steps last-hook ≤ Cost.rank (Node.driverState Fixture.after-done)
last-hook-bounded = Proof.shutdown-bounded last-hook (refl , refl)

-- This trace contains one operation despite already completed client work.
last-hook-count : Proof.steps last-hook ≡ 1
last-hook-count = refl

-- Its source has twelve potential credits, not a claimed twelve-second latency bound.
last-hook-budget : Cost.rank (Node.driverState Fixture.after-done) ≡ 12
last-hook-budget = refl

-- Full environment records can stutter after the same fresh production prefix.
repeat-input : (n : ℕ) → Node.Run Fixture.after-done
  (replicate n (Node.setForecast false)) Fixture.after-done
repeat-input zero = Node.stop
repeat-input (suc n) = Node.visible Node.forecastInput (repeat-input n)

-- Such input records are not silently counted as actual driver transitions.
input-stutters : ∀ n → Policy.driver-operations (repeat-input n) ≡ 0
input-stutters zero = refl
input-stutters (suc n) = input-stutters n

-- A bound on all visible node inputs by the driver potential would therefore be false.
input-count-exceeds-rank : Policy.rank Fixture.after-done <
  length (replicate 13 (Node.setForecast false))
input-count-exceeds-rank = ≤-refl

-- The precise projected-driver bound still accepts every one of those input schedules.
inputs-driver-bounded : ∀ n → Policy.driver-operations (repeat-input n) ≤ Policy.rank Fixture.after-done
inputs-driver-bounded n = Policy.shutdown-bounded (repeat-input n) (refl , refl)
